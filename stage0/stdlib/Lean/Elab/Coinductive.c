// Lean compiler output
// Module: Lean.Elab.Coinductive
// Imports: public import Lean.Elab.PreDefinition.PartialFixpoint public import Lean.Elab.Tactic.Rewrite public import Lean.Meta.Tactic.Simp public import Lean.Linter.UnusedVariables
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
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t, uint8_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_replace_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqMP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedModifiers_default;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Elab_Modifiers_filterAttrs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Elab_partialFixpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coinductive"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__1_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 250, 83, 200, 24, 179, 82, 22)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__3_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__4_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__6_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Coinductive"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__7_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 151, 120, 159, 3, 29, 155, 48)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__9_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(35, 130, 159, 181, 44, 62, 204, 36)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__10_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(110, 111, 66, 57, 94, 45, 50, 171)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__11_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(60, 175, 17, 102, 142, 128, 198, 201)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__12_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__13_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(9, 209, 191, 44, 117, 223, 160, 247)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__14_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__15_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 237, 174, 240, 153, 126, 239, 5)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__16_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__17_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 27, 51, 192, 193, 175, 235, 144)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__18_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__5_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 221, 168, 89, 68, 150, 234, 156)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__19_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__0_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 103, 123, 222, 186, 196, 147, 100)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__20_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__8_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 247, 171, 212, 36, 152, 75, 212)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__21_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)(((size_t)(793488904) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(116, 33, 50, 188, 4, 44, 82, 154)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__22_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__23_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 218, 6, 79, 1, 64, 32, 132)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__24_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__25_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 217, 196, 13, 214, 247, 225, 210)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__26_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(174, 151, 118, 109, 52, 19, 96, 242)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2____boxed(lean_object*);
static const lean_array_object l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0 = (const lean_object*)&l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_instInhabitedCoinductiveElabData;
static const lean_string_object l_Lean_Elab_Command_addFunctorPostfix___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_functor"};
static const lean_object* l_Lean_Elab_Command_addFunctorPostfix___closed__0 = (const lean_object*)&l_Lean_Elab_Command_addFunctorPostfix___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Command_addFunctorPostfix___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Command_addFunctorPostfix___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 229, 169, 91, 229, 240, 88, 134)}};
static const lean_object* l_Lean_Elab_Command_addFunctorPostfix___closed__1 = (const lean_object*)&l_Lean_Elab_Command_addFunctorPostfix___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addFunctorPostfix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfix(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(lean_object*);
static const lean_string_object l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Elab.Coinductive"};
static const lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0 = (const lean_object*)&l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0_value;
static const lean_string_object l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.Elab.Command.removeFunctorPostfixInCtor"};
static const lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1 = (const lean_object*)&l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1_value;
static const lean_string_object l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "UnexpectedName"};
static const lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2 = (const lean_object*)&l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "did not generate unfolding theorem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "existential_equiv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 65, 32, 87, 61, 118, 240, 105)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "functor_unfold"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 202, 245, 227, 23, 206, 217, 112)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "res: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "The conclusion of the constructor "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " is "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "The elaborated constructor is of the type: "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Generating constructor: "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Expected one argument"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cases_eliminator"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(244, 14, 239, 189, 147, 54, 173, 250)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elab_as_elim"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 49, 111, 107, 153, 28, 187, 88)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__4_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__7_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "expected to be quantifier"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object**);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "existential"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 178, 56, 87, 59, 132, 244, 77)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Command_elabCoinductive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Elaborating: "};
static const lean_object* l_Lean_Elab_Command_elabCoinductive___closed__0 = (const lean_object*)&l_Lean_Elab_Command_elabCoinductive___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Command_elabCoinductive___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Command_elabCoinductive___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_66_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_67_ = 0;
v___x_68_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__27_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_69_ = l_Lean_registerTraceClass(v___x_66_, v___x_67_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2____boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_();
return v_res_71_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1(void){
_start:
{
lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_74_ = lean_box(0);
v___x_75_ = 0;
v___x_76_ = ((lean_object*)(l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0));
v___x_77_ = l_Lean_Elab_instInhabitedModifiers_default;
v___x_78_ = lean_box(0);
v___x_79_ = lean_box(0);
v___x_80_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
lean_ctor_set(v___x_80_, 2, v___x_79_);
lean_ctor_set(v___x_80_, 3, v___x_77_);
lean_ctor_set(v___x_80_, 4, v___x_76_);
lean_ctor_set(v___x_80_, 5, v___x_74_);
lean_ctor_set_uint8(v___x_80_, sizeof(void*)*6, v___x_75_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1, &l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1_once, _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addFunctorPostfix(lean_object* v_x_86_){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Elab_Command_addFunctorPostfix___closed__1));
v___x_88_ = l_Lean_Name_append(v_x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfix(lean_object* v_x_89_){
_start:
{
uint8_t v___x_90_; 
v___x_90_ = l_Lean_Name_hasMacroScopes(v_x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Name_getPrefix(v_x_89_);
lean_dec(v_x_89_);
return v___x_91_;
}
else
{
lean_object* v_view_92_; lean_object* v_name_93_; lean_object* v_imported_94_; lean_object* v_ctx_95_; lean_object* v_scopes_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_105_; 
v_view_92_ = l_Lean_extractMacroScopes(v_x_89_);
v_name_93_ = lean_ctor_get(v_view_92_, 0);
v_imported_94_ = lean_ctor_get(v_view_92_, 1);
v_ctx_95_ = lean_ctor_get(v_view_92_, 2);
v_scopes_96_ = lean_ctor_get(v_view_92_, 3);
v_isSharedCheck_105_ = !lean_is_exclusive(v_view_92_);
if (v_isSharedCheck_105_ == 0)
{
v___x_98_ = v_view_92_;
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_scopes_96_);
lean_inc(v_ctx_95_);
lean_inc(v_imported_94_);
lean_inc(v_name_93_);
lean_dec(v_view_92_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_100_ = l_Lean_Name_getPrefix(v_name_93_);
lean_dec(v_name_93_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_100_);
v___x_102_ = v___x_98_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_100_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_imported_94_);
lean_ctor_set(v_reuseFailAlloc_104_, 2, v_ctx_95_);
lean_ctor_set(v_reuseFailAlloc_104_, 3, v_scopes_96_);
v___x_102_ = v_reuseFailAlloc_104_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_MacroScopesView_review(v___x_102_);
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(lean_object* v_msg_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_box(0);
v___x_108_ = lean_panic_fn_borrowed(v___x_107_, v_msg_106_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_112_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2));
v___x_113_ = lean_unsigned_to_nat(13u);
v___x_114_ = lean_unsigned_to_nat(126u);
v___x_115_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1));
v___x_116_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0));
v___x_117_ = l_mkPanicMessageWithDecl(v___x_116_, v___x_115_, v___x_114_, v___x_113_, v___x_112_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor(lean_object* v_x_118_){
_start:
{
if (lean_obj_tag(v_x_118_) == 1)
{
lean_object* v_pre_119_; lean_object* v_str_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_pre_119_ = lean_ctor_get(v_x_118_, 0);
lean_inc(v_pre_119_);
v_str_120_ = lean_ctor_get(v_x_118_, 1);
lean_inc_ref(v_str_120_);
lean_dec_ref_known(v_x_118_, 2);
v___x_121_ = l_Lean_Elab_Command_removeFunctorPostfix(v_pre_119_);
v___x_122_ = l_Lean_Name_str___override(v___x_121_, v_str_120_);
return v___x_122_;
}
else
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec(v_x_118_);
v___x_123_ = lean_obj_once(&l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3, &l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3_once, _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3);
v___x_124_ = l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(v___x_123_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(lean_object* v_goal_130_, lean_object* v_eq_131_, uint8_t v_symm_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
lean_inc(v_goal_130_);
v___x_138_ = l_Lean_MVarId_getType(v_goal_130_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v_goal_130_);
v___x_141_ = l_Lean_MVarId_rewrite(v_goal_130_, v_a_139_, v_eq_131_, v_symm_132_, v___x_140_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_141_) == 0)
{
lean_object* v_a_142_; lean_object* v_eNew_143_; lean_object* v_eqProof_144_; lean_object* v___x_145_; 
v_a_142_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v___x_141_, 1);
v_eNew_143_ = lean_ctor_get(v_a_142_, 0);
lean_inc_ref(v_eNew_143_);
v_eqProof_144_ = lean_ctor_get(v_a_142_, 1);
lean_inc_ref(v_eqProof_144_);
lean_dec(v_a_142_);
v___x_145_ = l_Lean_MVarId_replaceTargetEq(v_goal_130_, v_eNew_143_, v_eqProof_144_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
return v___x_145_;
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_goal_130_);
v_a_146_ = lean_ctor_get(v___x_141_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_141_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_141_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_141_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref(v_eq_131_);
lean_dec(v_goal_130_);
v_a_154_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_138_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_138_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___boxed(lean_object* v_goal_162_, lean_object* v_eq_163_, lean_object* v_symm_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
uint8_t v_symm_boxed_170_; lean_object* v_res_171_; 
v_symm_boxed_170_ = lean_unbox(v_symm_164_);
v_res_171_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v_goal_162_, v_eq_163_, v_symm_boxed_170_, v_a_165_, v_a_166_, v_a_167_, v_a_168_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(lean_object* v_e_172_, lean_object* v___y_173_){
_start:
{
uint8_t v___x_175_; 
v___x_175_ = l_Lean_Expr_hasMVar(v_e_172_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v_e_172_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v_mctx_178_; lean_object* v___x_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_182_; lean_object* v_cache_183_; lean_object* v_zetaDeltaFVarIds_184_; lean_object* v_postponed_185_; lean_object* v_diag_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
v___x_177_ = lean_st_ref_get(v___y_173_);
v_mctx_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc_ref(v_mctx_178_);
lean_dec(v___x_177_);
v___x_179_ = l_Lean_instantiateMVarsCore(v_mctx_178_, v_e_172_);
v_fst_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_fst_180_);
v_snd_181_ = lean_ctor_get(v___x_179_, 1);
lean_inc(v_snd_181_);
lean_dec_ref(v___x_179_);
v___x_182_ = lean_st_ref_take(v___y_173_);
v_cache_183_ = lean_ctor_get(v___x_182_, 1);
v_zetaDeltaFVarIds_184_ = lean_ctor_get(v___x_182_, 2);
v_postponed_185_ = lean_ctor_get(v___x_182_, 3);
v_diag_186_ = lean_ctor_get(v___x_182_, 4);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_195_ == 0)
{
lean_object* v_unused_196_; 
v_unused_196_ = lean_ctor_get(v___x_182_, 0);
lean_dec(v_unused_196_);
v___x_188_ = v___x_182_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_diag_186_);
lean_inc(v_postponed_185_);
lean_inc(v_zetaDeltaFVarIds_184_);
lean_inc(v_cache_183_);
lean_dec(v___x_182_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 0, v_snd_181_);
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_snd_181_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_cache_183_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_zetaDeltaFVarIds_184_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_postponed_185_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v_diag_186_);
v___x_191_ = v_reuseFailAlloc_194_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_st_ref_put(v___y_173_, v___x_191_);
v___x_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_193_, 0, v_fst_180_);
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg___boxed(lean_object* v_e_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_197_, v___y_198_);
lean_dec(v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(lean_object* v_e_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_201_, v___y_203_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___boxed(lean_object* v_e_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(v_e_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(lean_object* v_k_215_, lean_object* v_b_216_, lean_object* v_c_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
lean_inc(v___y_221_);
lean_inc_ref(v___y_220_);
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
v___x_223_ = lean_apply_7(v_k_215_, v_b_216_, v_c_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, lean_box(0));
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed(lean_object* v_k_224_, lean_object* v_b_225_, lean_object* v_c_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(v_k_224_, v_b_225_, v_c_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(lean_object* v_type_233_, lean_object* v_k_234_, uint8_t v_cleanupAnnotations_235_, uint8_t v_whnfType_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; 
v___f_242_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_242_, 0, v_k_234_);
v___x_243_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_233_, v___f_242_, v_cleanupAnnotations_235_, v_whnfType_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_243_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_243_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
else
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_259_; 
v_a_252_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_259_ == 0)
{
v___x_254_ = v___x_243_;
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_243_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_259_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_257_; 
if (v_isShared_255_ == 0)
{
v___x_257_ = v___x_254_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_a_252_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___boxed(lean_object* v_type_260_, lean_object* v_k_261_, lean_object* v_cleanupAnnotations_262_, lean_object* v_whnfType_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_269_; uint8_t v_whnfType_boxed_270_; lean_object* v_res_271_; 
v_cleanupAnnotations_boxed_269_ = lean_unbox(v_cleanupAnnotations_262_);
v_whnfType_boxed_270_ = lean_unbox(v_whnfType_263_);
v_res_271_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_260_, v_k_261_, v_cleanupAnnotations_boxed_269_, v_whnfType_boxed_270_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(lean_object* v_00_u03b1_272_, lean_object* v_type_273_, lean_object* v_k_274_, uint8_t v_cleanupAnnotations_275_, uint8_t v_whnfType_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_273_, v_k_274_, v_cleanupAnnotations_275_, v_whnfType_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___boxed(lean_object* v_00_u03b1_283_, lean_object* v_type_284_, lean_object* v_k_285_, lean_object* v_cleanupAnnotations_286_, lean_object* v_whnfType_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_293_; uint8_t v_whnfType_boxed_294_; lean_object* v_res_295_; 
v_cleanupAnnotations_boxed_293_ = lean_unbox(v_cleanupAnnotations_286_);
v_whnfType_boxed_294_ = lean_unbox(v_whnfType_287_);
v_res_295_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(v_00_u03b1_283_, v_type_284_, v_k_285_, v_cleanupAnnotations_boxed_293_, v_whnfType_boxed_294_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(lean_object* v_name_296_, lean_object* v_levelParams_297_, lean_object* v_type_298_, lean_object* v_value_299_, lean_object* v_hints_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; uint8_t v___y_305_; lean_object* v_env_313_; uint8_t v___x_314_; 
v___x_303_ = lean_st_ref_get(v___y_301_);
v_env_313_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref_n(v_env_313_, 2);
lean_dec(v___x_303_);
v___x_314_ = l_Lean_Environment_hasUnsafe(v_env_313_, v_type_298_);
if (v___x_314_ == 0)
{
uint8_t v___x_315_; 
v___x_315_ = l_Lean_Environment_hasUnsafe(v_env_313_, v_value_299_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = 1;
v___y_305_ = v___x_316_;
goto v___jp_304_;
}
else
{
goto v___jp_311_;
}
}
else
{
lean_dec_ref(v_env_313_);
goto v___jp_311_;
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
lean_inc(v_name_296_);
v___x_306_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_306_, 0, v_name_296_);
lean_ctor_set(v___x_306_, 1, v_levelParams_297_);
lean_ctor_set(v___x_306_, 2, v_type_298_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_308_, 0, v_name_296_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_309_, 0, v___x_306_);
lean_ctor_set(v___x_309_, 1, v_value_299_);
lean_ctor_set(v___x_309_, 2, v_hints_300_);
lean_ctor_set(v___x_309_, 3, v___x_308_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*4, v___y_305_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
v___jp_311_:
{
uint8_t v___x_312_; 
v___x_312_ = 0;
v___y_305_ = v___x_312_;
goto v___jp_304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg___boxed(lean_object* v_name_317_, lean_object* v_levelParams_318_, lean_object* v_type_319_, lean_object* v_value_320_, lean_object* v_hints_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_317_, v_levelParams_318_, v_type_319_, v_value_320_, v_hints_321_, v___y_322_);
lean_dec(v___y_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(lean_object* v_name_325_, lean_object* v_levelParams_326_, lean_object* v_type_327_, lean_object* v_value_328_, lean_object* v_hints_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_325_, v_levelParams_326_, v_type_327_, v_value_328_, v_hints_329_, v___y_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___boxed(lean_object* v_name_336_, lean_object* v_levelParams_337_, lean_object* v_type_338_, lean_object* v_value_339_, lean_object* v_hints_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(v_name_336_, v_levelParams_337_, v_type_338_, v_value_339_, v_hints_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
if (lean_obj_tag(v_a_347_) == 0)
{
lean_object* v___x_349_; 
v___x_349_ = l_List_reverse___redArg(v_a_348_);
return v___x_349_;
}
else
{
lean_object* v_head_350_; lean_object* v_tail_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_360_; 
v_head_350_ = lean_ctor_get(v_a_347_, 0);
v_tail_351_ = lean_ctor_get(v_a_347_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v_a_347_);
if (v_isSharedCheck_360_ == 0)
{
v___x_353_ = v_a_347_;
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_tail_351_);
lean_inc(v_head_350_);
lean_dec(v_a_347_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_360_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_357_; 
v___x_355_ = l_Lean_mkLevelParam(v_head_350_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_a_348_);
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_357_ = v___x_353_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_a_348_);
v___x_357_ = v_reuseFailAlloc_359_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
v_a_347_ = v_tail_351_;
v_a_348_ = v___x_357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_){
_start:
{
lean_object* v_ks_365_; lean_object* v_vs_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_390_; 
v_ks_365_ = lean_ctor_get(v_x_361_, 0);
v_vs_366_ = lean_ctor_get(v_x_361_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_x_361_);
if (v_isSharedCheck_390_ == 0)
{
v___x_368_ = v_x_361_;
v_isShared_369_ = v_isSharedCheck_390_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_vs_366_);
lean_inc(v_ks_365_);
lean_dec(v_x_361_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_390_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = lean_array_get_size(v_ks_365_);
v___x_371_ = lean_nat_dec_lt(v_x_362_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
lean_dec(v_x_362_);
v___x_372_ = lean_array_push(v_ks_365_, v_x_363_);
v___x_373_ = lean_array_push(v_vs_366_, v_x_364_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_373_);
lean_ctor_set(v___x_368_, 0, v___x_372_);
v___x_375_ = v___x_368_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
else
{
lean_object* v_k_x27_377_; uint8_t v___x_378_; 
v_k_x27_377_ = lean_array_fget_borrowed(v_ks_365_, v_x_362_);
v___x_378_ = l_Lean_instBEqMVarId_beq(v_x_363_, v_k_x27_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_380_; 
if (v_isShared_369_ == 0)
{
v___x_380_ = v___x_368_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_ks_365_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_vs_366_);
v___x_380_ = v_reuseFailAlloc_384_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_add(v_x_362_, v___x_381_);
lean_dec(v_x_362_);
v_x_361_ = v___x_380_;
v_x_362_ = v___x_382_;
goto _start;
}
}
else
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_385_ = lean_array_fset(v_ks_365_, v_x_362_, v_x_363_);
v___x_386_ = lean_array_fset(v_vs_366_, v_x_362_, v_x_364_);
lean_dec(v_x_362_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_386_);
lean_ctor_set(v___x_368_, 0, v___x_385_);
v___x_388_ = v___x_368_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_385_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(lean_object* v_n_391_, lean_object* v_k_392_, lean_object* v_v_393_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_n_391_, v___x_394_, v_k_392_, v_v_393_);
return v___x_395_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(lean_object* v_x_397_, size_t v_x_398_, size_t v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
lean_object* v_es_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v_j_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_es_402_ = lean_ctor_get(v_x_397_, 0);
v___x_403_ = ((size_t)31ULL);
v___x_404_ = lean_usize_land(v_x_398_, v___x_403_);
v_j_405_ = lean_usize_to_nat(v___x_404_);
v___x_406_ = lean_array_get_size(v_es_402_);
v___x_407_ = lean_nat_dec_lt(v_j_405_, v___x_406_);
if (v___x_407_ == 0)
{
lean_dec(v_j_405_);
lean_dec(v_x_401_);
lean_dec(v_x_400_);
return v_x_397_;
}
else
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_446_; 
lean_inc_ref(v_es_402_);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_397_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v_x_397_, 0);
lean_dec(v_unused_447_);
v___x_409_ = v_x_397_;
v_isShared_410_ = v_isSharedCheck_446_;
goto v_resetjp_408_;
}
else
{
lean_dec(v_x_397_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_446_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_v_411_; lean_object* v___x_412_; lean_object* v_xs_x27_413_; lean_object* v___y_415_; 
v_v_411_ = lean_array_fget(v_es_402_, v_j_405_);
v___x_412_ = lean_box(0);
v_xs_x27_413_ = lean_array_fset(v_es_402_, v_j_405_, v___x_412_);
switch(lean_obj_tag(v_v_411_))
{
case 0:
{
lean_object* v_key_420_; lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_431_; 
v_key_420_ = lean_ctor_get(v_v_411_, 0);
v_val_421_ = lean_ctor_get(v_v_411_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_v_411_);
if (v_isSharedCheck_431_ == 0)
{
v___x_423_ = v_v_411_;
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_val_421_);
lean_inc(v_key_420_);
lean_dec(v_v_411_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_431_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
uint8_t v___x_425_; 
v___x_425_ = l_Lean_instBEqMVarId_beq(v_x_400_, v_key_420_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; 
lean_del_object(v___x_423_);
v___x_426_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_420_, v_val_421_, v_x_400_, v_x_401_);
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
v___y_415_ = v___x_427_;
goto v___jp_414_;
}
else
{
lean_object* v___x_429_; 
lean_dec(v_val_421_);
lean_dec(v_key_420_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 1, v_x_401_);
lean_ctor_set(v___x_423_, 0, v_x_400_);
v___x_429_ = v___x_423_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_x_400_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_x_401_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
v___y_415_ = v___x_429_;
goto v___jp_414_;
}
}
}
}
case 1:
{
lean_object* v_node_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_444_; 
v_node_432_ = lean_ctor_get(v_v_411_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_v_411_);
if (v_isSharedCheck_444_ == 0)
{
v___x_434_ = v_v_411_;
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_node_432_);
lean_dec(v_v_411_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
size_t v___x_436_; size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_436_ = ((size_t)5ULL);
v___x_437_ = lean_usize_shift_right(v_x_398_, v___x_436_);
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_x_399_, v___x_438_);
v___x_440_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_node_432_, v___x_437_, v___x_439_, v_x_400_, v_x_401_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_440_);
v___x_442_ = v___x_434_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
v___y_415_ = v___x_442_;
goto v___jp_414_;
}
}
}
default: 
{
lean_object* v___x_445_; 
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_x_400_);
lean_ctor_set(v___x_445_, 1, v_x_401_);
v___y_415_ = v___x_445_;
goto v___jp_414_;
}
}
v___jp_414_:
{
lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_416_ = lean_array_fset(v_xs_x27_413_, v_j_405_, v___y_415_);
lean_dec(v_j_405_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_416_);
v___x_418_ = v___x_409_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
else
{
lean_object* v_ks_448_; lean_object* v_vs_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_467_; 
v_ks_448_ = lean_ctor_get(v_x_397_, 0);
v_vs_449_ = lean_ctor_get(v_x_397_, 1);
v_isSharedCheck_467_ = !lean_is_exclusive(v_x_397_);
if (v_isSharedCheck_467_ == 0)
{
v___x_451_ = v_x_397_;
v_isShared_452_ = v_isSharedCheck_467_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_vs_449_);
lean_inc(v_ks_448_);
lean_dec(v_x_397_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_467_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v_ks_448_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_vs_449_);
v___x_454_ = v_reuseFailAlloc_466_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v_newNode_455_; size_t v___x_456_; uint8_t v___x_457_; 
v_newNode_455_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v___x_454_, v_x_400_, v_x_401_);
v___x_456_ = ((size_t)7ULL);
v___x_457_ = lean_usize_dec_le(v___x_456_, v_x_399_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v___x_458_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_455_);
v___x_459_ = lean_unsigned_to_nat(4u);
v___x_460_ = lean_nat_dec_lt(v___x_458_, v___x_459_);
lean_dec(v___x_458_);
if (v___x_460_ == 0)
{
lean_object* v_ks_461_; lean_object* v_vs_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_ks_461_ = lean_ctor_get(v_newNode_455_, 0);
lean_inc_ref(v_ks_461_);
v_vs_462_ = lean_ctor_get(v_newNode_455_, 1);
lean_inc_ref(v_vs_462_);
lean_dec_ref(v_newNode_455_);
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0);
v___x_465_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_x_399_, v_ks_461_, v_vs_462_, v___x_463_, v___x_464_);
lean_dec_ref(v_vs_462_);
lean_dec_ref(v_ks_461_);
return v___x_465_;
}
else
{
return v_newNode_455_;
}
}
else
{
return v_newNode_455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(size_t v_depth_468_, lean_object* v_keys_469_, lean_object* v_vals_470_, lean_object* v_i_471_, lean_object* v_entries_472_){
_start:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_array_get_size(v_keys_469_);
v___x_474_ = lean_nat_dec_lt(v_i_471_, v___x_473_);
if (v___x_474_ == 0)
{
lean_dec(v_i_471_);
return v_entries_472_;
}
else
{
lean_object* v_k_475_; lean_object* v_v_476_; uint64_t v___x_477_; size_t v_h_478_; size_t v___x_479_; lean_object* v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v_h_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_k_475_ = lean_array_fget_borrowed(v_keys_469_, v_i_471_);
v_v_476_ = lean_array_fget_borrowed(v_vals_470_, v_i_471_);
v___x_477_ = l_Lean_instHashableMVarId_hash(v_k_475_);
v_h_478_ = lean_uint64_to_usize(v___x_477_);
v___x_479_ = ((size_t)5ULL);
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_sub(v_depth_468_, v___x_481_);
v___x_483_ = lean_usize_mul(v___x_479_, v___x_482_);
v_h_484_ = lean_usize_shift_right(v_h_478_, v___x_483_);
v___x_485_ = lean_nat_add(v_i_471_, v___x_480_);
lean_dec(v_i_471_);
lean_inc(v_v_476_);
lean_inc(v_k_475_);
v___x_486_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_entries_472_, v_h_484_, v_depth_468_, v_k_475_, v_v_476_);
v_i_471_ = v___x_485_;
v_entries_472_ = v___x_486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_depth_488_, lean_object* v_keys_489_, lean_object* v_vals_490_, lean_object* v_i_491_, lean_object* v_entries_492_){
_start:
{
size_t v_depth_boxed_493_; lean_object* v_res_494_; 
v_depth_boxed_493_ = lean_unbox_usize(v_depth_488_);
lean_dec(v_depth_488_);
v_res_494_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_boxed_493_, v_keys_489_, v_vals_490_, v_i_491_, v_entries_492_);
lean_dec_ref(v_vals_490_);
lean_dec_ref(v_keys_489_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_495_, lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
size_t v_x_8837__boxed_500_; size_t v_x_8838__boxed_501_; lean_object* v_res_502_; 
v_x_8837__boxed_500_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_x_8838__boxed_501_ = lean_unbox_usize(v_x_497_);
lean_dec(v_x_497_);
v_res_502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_495_, v_x_8837__boxed_500_, v_x_8838__boxed_501_, v_x_498_, v_x_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_){
_start:
{
uint64_t v___x_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_506_ = l_Lean_instHashableMVarId_hash(v_x_504_);
v___x_507_ = lean_uint64_to_usize(v___x_506_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_503_, v___x_507_, v___x_508_, v_x_504_, v_x_505_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object* v_mvarId_510_, lean_object* v_val_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v_mctx_515_; lean_object* v_cache_516_; lean_object* v_zetaDeltaFVarIds_517_; lean_object* v_postponed_518_; lean_object* v_diag_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_549_; 
v___x_514_ = lean_st_ref_take(v___y_512_);
v_mctx_515_ = lean_ctor_get(v___x_514_, 0);
v_cache_516_ = lean_ctor_get(v___x_514_, 1);
v_zetaDeltaFVarIds_517_ = lean_ctor_get(v___x_514_, 2);
v_postponed_518_ = lean_ctor_get(v___x_514_, 3);
v_diag_519_ = lean_ctor_get(v___x_514_, 4);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_549_ == 0)
{
v___x_521_ = v___x_514_;
v_isShared_522_ = v_isSharedCheck_549_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_diag_519_);
lean_inc(v_postponed_518_);
lean_inc(v_zetaDeltaFVarIds_517_);
lean_inc(v_cache_516_);
lean_inc(v_mctx_515_);
lean_dec(v___x_514_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_549_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_depth_523_; lean_object* v_levelAssignDepth_524_; lean_object* v_lmvarCounter_525_; lean_object* v_mvarCounter_526_; lean_object* v_lDecls_527_; lean_object* v_decls_528_; lean_object* v_userNames_529_; lean_object* v_lAssignment_530_; lean_object* v_eAssignment_531_; lean_object* v_dAssignment_532_; lean_object* v_instanceTypedMVars_533_; lean_object* v_synthNormMemo_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_548_; 
v_depth_523_ = lean_ctor_get(v_mctx_515_, 0);
v_levelAssignDepth_524_ = lean_ctor_get(v_mctx_515_, 1);
v_lmvarCounter_525_ = lean_ctor_get(v_mctx_515_, 2);
v_mvarCounter_526_ = lean_ctor_get(v_mctx_515_, 3);
v_lDecls_527_ = lean_ctor_get(v_mctx_515_, 4);
v_decls_528_ = lean_ctor_get(v_mctx_515_, 5);
v_userNames_529_ = lean_ctor_get(v_mctx_515_, 6);
v_lAssignment_530_ = lean_ctor_get(v_mctx_515_, 7);
v_eAssignment_531_ = lean_ctor_get(v_mctx_515_, 8);
v_dAssignment_532_ = lean_ctor_get(v_mctx_515_, 9);
v_instanceTypedMVars_533_ = lean_ctor_get(v_mctx_515_, 10);
v_synthNormMemo_534_ = lean_ctor_get(v_mctx_515_, 11);
v_isSharedCheck_548_ = !lean_is_exclusive(v_mctx_515_);
if (v_isSharedCheck_548_ == 0)
{
v___x_536_ = v_mctx_515_;
v_isShared_537_ = v_isSharedCheck_548_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_synthNormMemo_534_);
lean_inc(v_instanceTypedMVars_533_);
lean_inc(v_dAssignment_532_);
lean_inc(v_eAssignment_531_);
lean_inc(v_lAssignment_530_);
lean_inc(v_userNames_529_);
lean_inc(v_decls_528_);
lean_inc(v_lDecls_527_);
lean_inc(v_mvarCounter_526_);
lean_inc(v_lmvarCounter_525_);
lean_inc(v_levelAssignDepth_524_);
lean_inc(v_depth_523_);
lean_dec(v_mctx_515_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_548_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_538_ = lean_box(0);
v___x_539_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_531_, v_mvarId_510_, v_val_511_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 8, v___x_539_);
v___x_541_ = v___x_536_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_depth_523_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_levelAssignDepth_524_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_lmvarCounter_525_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_mvarCounter_526_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_lDecls_527_);
lean_ctor_set(v_reuseFailAlloc_547_, 5, v_decls_528_);
lean_ctor_set(v_reuseFailAlloc_547_, 6, v_userNames_529_);
lean_ctor_set(v_reuseFailAlloc_547_, 7, v_lAssignment_530_);
lean_ctor_set(v_reuseFailAlloc_547_, 8, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_547_, 9, v_dAssignment_532_);
lean_ctor_set(v_reuseFailAlloc_547_, 10, v_instanceTypedMVars_533_);
lean_ctor_set(v_reuseFailAlloc_547_, 11, v_synthNormMemo_534_);
v___x_541_ = v_reuseFailAlloc_547_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_541_);
v___x_543_ = v___x_521_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_cache_516_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_zetaDeltaFVarIds_517_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_postponed_518_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_diag_519_);
v___x_543_ = v_reuseFailAlloc_546_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_st_ref_put(v___y_512_, v___x_543_);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_538_);
return v___x_545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object* v_mvarId_550_, lean_object* v_val_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_550_, v_val_551_, v___y_552_);
lean_dec(v___y_552_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object* v_msgData_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v___x_561_; lean_object* v_env_562_; uint8_t v___x_563_; lean_object* v_env_564_; lean_object* v___x_565_; lean_object* v_toCold_566_; lean_object* v_mctx_567_; lean_object* v_lctx_568_; lean_object* v_options_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_561_ = lean_st_ref_get(v___y_559_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_563_ = 0;
v_env_564_ = l_Lean_Environment_setRecordingDeps(v_env_562_, v___x_563_);
v___x_565_ = lean_st_ref_get(v___y_557_);
v_toCold_566_ = lean_ctor_get(v___y_558_, 0);
v_mctx_567_ = lean_ctor_get(v___x_565_, 0);
lean_inc_ref(v_mctx_567_);
lean_dec(v___x_565_);
v_lctx_568_ = lean_ctor_get(v___y_556_, 2);
v_options_569_ = lean_ctor_get(v_toCold_566_, 2);
lean_inc_ref(v_options_569_);
lean_inc_ref(v_lctx_568_);
v___x_570_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_570_, 0, v_env_564_);
lean_ctor_set(v___x_570_, 1, v_mctx_567_);
lean_ctor_set(v___x_570_, 2, v_lctx_568_);
lean_ctor_set(v___x_570_, 3, v_options_569_);
v___x_571_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_msgData_555_);
v___x_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_ref_586_; lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
v_ref_586_ = lean_ctor_get(v___y_583_, 2);
v___x_587_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
lean_inc(v_ref_586_);
v___x_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_592_, 0, v_ref_586_);
lean_ctor_set(v___x_592_, 1, v_a_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set_tag(v___x_590_, 1);
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_604_, lean_object* v_b_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
lean_object* v_array_611_; lean_object* v_start_612_; lean_object* v_stop_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_628_; 
v_array_611_ = lean_ctor_get(v_a_604_, 0);
v_start_612_ = lean_ctor_get(v_a_604_, 1);
v_stop_613_ = lean_ctor_get(v_a_604_, 2);
v_isSharedCheck_628_ = !lean_is_exclusive(v_a_604_);
if (v_isSharedCheck_628_ == 0)
{
v___x_615_ = v_a_604_;
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_stop_613_);
lean_inc(v_start_612_);
lean_inc(v_array_611_);
lean_dec(v_a_604_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_628_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_lt(v_start_612_, v_stop_613_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_del_object(v___x_615_);
lean_dec(v_stop_613_);
lean_dec(v_start_612_);
lean_dec_ref(v_array_611_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_b_605_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_add(v_start_612_, v___x_619_);
lean_inc_ref(v_array_611_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v___x_620_);
v___x_622_ = v___x_615_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_array_611_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_stop_613_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_array_fget(v_array_611_, v_start_612_);
lean_dec(v_start_612_);
lean_dec_ref(v_array_611_);
v___x_624_ = l_Lean_Meta_mkCongrFun(v_b_605_, v___x_623_, v___y_606_, v___y_607_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_624_, 1);
v_a_604_ = v___x_622_;
v_b_605_ = v_a_625_;
goto _start;
}
else
{
lean_dec_ref(v___x_622_);
return v___x_624_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_629_, lean_object* v_b_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_629_, v_b_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_637_, lean_object* v___x_638_, size_t v_sz_639_, size_t v_i_640_, lean_object* v_bs_641_){
_start:
{
uint8_t v___x_642_; 
v___x_642_ = lean_usize_dec_lt(v_i_640_, v_sz_639_);
if (v___x_642_ == 0)
{
lean_dec(v_levels_637_);
return v_bs_641_;
}
else
{
lean_object* v_v_643_; lean_object* v_toConstantVal_644_; lean_object* v_name_645_; lean_object* v___x_646_; lean_object* v_bs_x27_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; 
v_v_643_ = lean_array_uget_borrowed(v_bs_641_, v_i_640_);
v_toConstantVal_644_ = lean_ctor_get(v_v_643_, 0);
v_name_645_ = lean_ctor_get(v_toConstantVal_644_, 0);
lean_inc(v_name_645_);
v___x_646_ = lean_unsigned_to_nat(0u);
v_bs_x27_647_ = lean_array_uset(v_bs_641_, v_i_640_, v___x_646_);
v___x_648_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_645_);
lean_inc(v_levels_637_);
v___x_649_ = l_Lean_mkConst(v___x_648_, v_levels_637_);
v___x_650_ = l_Lean_mkAppN(v___x_649_, v___x_638_);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_640_, v___x_651_);
v___x_653_ = lean_array_uset(v_bs_x27_647_, v_i_640_, v___x_650_);
v_i_640_ = v___x_652_;
v_bs_641_ = v___x_653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_655_, lean_object* v___x_656_, lean_object* v_sz_657_, lean_object* v_i_658_, lean_object* v_bs_659_){
_start:
{
size_t v_sz_boxed_660_; size_t v_i_boxed_661_; lean_object* v_res_662_; 
v_sz_boxed_660_ = lean_unbox_usize(v_sz_657_);
lean_dec(v_sz_657_);
v_i_boxed_661_ = lean_unbox_usize(v_i_658_);
lean_dec(v_i_658_);
v_res_662_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_655_, v___x_656_, v_sz_boxed_660_, v_i_boxed_661_, v_bs_659_);
lean_dec_ref(v___x_656_);
return v_res_662_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0));
v___x_665_ = l_Lean_stringToMessageData(v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object* v_infos_669_, lean_object* v_numParams_670_, lean_object* v___x_671_, lean_object* v_name_672_, lean_object* v_levels_673_, lean_object* v_args_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; size_t v_sz_699_; size_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_688_ = lean_array_get_size(v_infos_669_);
v___x_689_ = lean_nat_sub(v_numParams_670_, v___x_688_);
lean_inc(v___x_671_);
lean_inc_ref(v_args_674_);
v___x_690_ = l_Array_toSubarray___redArg(v_args_674_, v___x_671_, v___x_689_);
v___x_691_ = lean_array_get_size(v_args_674_);
v___x_692_ = l_Array_toSubarray___redArg(v_args_674_, v_numParams_670_, v___x_691_);
lean_inc_n(v_name_672_, 2);
v___x_693_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_672_);
lean_inc_n(v_levels_673_, 3);
lean_inc(v___x_693_);
v___x_694_ = l_Lean_mkConst(v___x_693_, v_levels_673_);
v___x_695_ = l_Subarray_copy___redArg(v___x_690_);
v___x_696_ = l_Lean_mkAppN(v___x_694_, v___x_695_);
lean_inc_ref(v___x_692_);
v___x_697_ = l_Subarray_copy___redArg(v___x_692_);
v___x_698_ = l_Lean_mkAppN(v___x_696_, v___x_697_);
v_sz_699_ = lean_array_size(v_infos_669_);
v___x_700_ = ((size_t)0ULL);
v___x_701_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_673_, v___x_695_, v_sz_699_, v___x_700_, v_infos_669_);
v___x_702_ = l_Lean_mkConst(v_name_672_, v_levels_673_);
lean_inc_ref(v___x_695_);
v___x_703_ = l_Array_append___redArg(v___x_695_, v___x_701_);
lean_dec_ref(v___x_701_);
v___x_704_ = l_Array_append___redArg(v___x_703_, v___x_697_);
v___x_705_ = l_Lean_mkAppN(v___x_702_, v___x_704_);
lean_dec_ref(v___x_704_);
v___x_706_ = l_Lean_Meta_mkEq(v___x_698_, v___x_705_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_766_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_766_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_766_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_766_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set_tag(v___x_709_, 1);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_765_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = 0;
v___x_714_ = lean_box(0);
v___x_715_ = l_Lean_Meta_mkFreshExprMVar(v___x_712_, v___x_713_, v___x_714_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v_a_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
v_a_716_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_a_716_);
lean_dec_ref_known(v___x_715_, 1);
v___x_717_ = l_Lean_Expr_mvarId_x21(v_a_716_);
v___x_718_ = l_Lean_Meta_getEqnsFor_x3f(v___x_693_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
lean_inc(v_a_719_);
lean_dec_ref_known(v___x_718_, 1);
if (lean_obj_tag(v_a_719_) == 1)
{
lean_object* v_val_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_val_720_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_val_720_);
lean_dec_ref_known(v_a_719_, 1);
v___x_721_ = lean_array_get_size(v_val_720_);
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_dec_eq(v___x_721_, v___x_722_);
if (v___x_723_ == 0)
{
lean_dec(v_val_720_);
lean_dec(v___x_717_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_692_);
lean_dec(v_levels_673_);
lean_dec(v_name_672_);
lean_dec(v___x_671_);
v___y_682_ = v___y_676_;
v___y_683_ = v___y_677_;
v___y_684_ = v___y_678_;
v___y_685_ = v___y_679_;
goto v___jp_681_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_724_ = lean_array_fget(v_val_720_, v___x_671_);
lean_dec(v___x_671_);
lean_dec(v_val_720_);
v___x_725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3));
v___x_726_ = l_Lean_Name_append(v_name_672_, v___x_725_);
lean_inc(v_levels_673_);
v___x_727_ = l_Lean_mkConst(v___x_726_, v_levels_673_);
v___x_728_ = l_Lean_mkConst(v___x_724_, v_levels_673_);
v___x_729_ = l_Lean_mkAppN(v___x_728_, v___x_695_);
v___x_730_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_692_, v___x_729_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; uint8_t v___x_732_; lean_object* v___x_733_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = 0;
v___x_733_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_717_, v___x_727_, v___x_732_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_734_, v_a_731_, v___y_677_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_736_; 
lean_dec_ref_known(v___x_735_, 1);
v___x_736_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_716_, v___y_677_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Array_append___redArg(v___x_695_, v___x_697_);
lean_dec_ref(v___x_697_);
v___x_739_ = 1;
v___x_740_ = l_Lean_Meta_mkLambdaFVars(v___x_738_, v_a_737_, v___x_732_, v___x_723_, v___x_732_, v___x_723_, v___x_739_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec_ref(v___x_738_);
return v___x_740_;
}
else
{
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
return v___x_736_;
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v_a_716_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
v_a_741_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_735_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_735_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v_a_731_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
v_a_749_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_733_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_733_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_dec_ref(v___x_727_);
lean_dec(v___x_717_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
return v___x_730_;
}
}
}
else
{
lean_dec(v_a_719_);
lean_dec(v___x_717_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_692_);
lean_dec(v_levels_673_);
lean_dec(v_name_672_);
lean_dec(v___x_671_);
v___y_682_ = v___y_676_;
v___y_683_ = v___y_677_;
v___y_684_ = v___y_678_;
v___y_685_ = v___y_679_;
goto v___jp_681_;
}
}
else
{
lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_764_; 
lean_dec(v___x_717_);
lean_dec(v_a_716_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_dec_ref(v___x_692_);
lean_dec(v_levels_673_);
lean_dec(v_name_672_);
lean_dec(v___x_671_);
v_a_757_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_764_ == 0)
{
v___x_759_ = v___x_718_;
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_718_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_764_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_762_; 
if (v_isShared_760_ == 0)
{
v___x_762_ = v___x_759_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_757_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
else
{
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_dec(v___x_693_);
lean_dec_ref(v___x_692_);
lean_dec(v_levels_673_);
lean_dec(v_name_672_);
lean_dec(v___x_671_);
return v___x_715_;
}
}
}
}
else
{
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_695_);
lean_dec(v___x_693_);
lean_dec_ref(v___x_692_);
lean_dec(v_levels_673_);
lean_dec(v_name_672_);
lean_dec(v___x_671_);
return v___x_706_;
}
v___jp_681_:
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
v___x_687_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_686_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object* v_infos_767_, lean_object* v_numParams_768_, lean_object* v___x_769_, lean_object* v_name_770_, lean_object* v_levels_771_, lean_object* v_args_772_, lean_object* v_x_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_767_, v_numParams_768_, v___x_769_, v_name_770_, v_levels_771_, v_args_772_, v_x_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec_ref(v_x_773_);
return v_res_779_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0(void){
_start:
{
lean_object* v___x_780_; double v___x_781_; 
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_float_of_nat(v___x_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_785_, lean_object* v_msg_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_ref_792_; lean_object* v___x_793_; lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_839_; 
v_ref_792_ = lean_ctor_get(v___y_789_, 2);
v___x_793_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_839_ == 0)
{
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_839_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_839_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v_traceState_799_; lean_object* v_env_800_; lean_object* v_nextMacroScope_801_; lean_object* v_ngen_802_; lean_object* v_auxDeclNGen_803_; lean_object* v_cache_804_; lean_object* v_recordedDeps_805_; lean_object* v_messages_806_; lean_object* v_infoState_807_; lean_object* v_snapshotTasks_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_838_; 
v___x_798_ = lean_st_ref_take(v___y_790_);
v_traceState_799_ = lean_ctor_get(v___x_798_, 4);
v_env_800_ = lean_ctor_get(v___x_798_, 0);
v_nextMacroScope_801_ = lean_ctor_get(v___x_798_, 1);
v_ngen_802_ = lean_ctor_get(v___x_798_, 2);
v_auxDeclNGen_803_ = lean_ctor_get(v___x_798_, 3);
v_cache_804_ = lean_ctor_get(v___x_798_, 5);
v_recordedDeps_805_ = lean_ctor_get(v___x_798_, 6);
v_messages_806_ = lean_ctor_get(v___x_798_, 7);
v_infoState_807_ = lean_ctor_get(v___x_798_, 8);
v_snapshotTasks_808_ = lean_ctor_get(v___x_798_, 9);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_838_ == 0)
{
v___x_810_ = v___x_798_;
v_isShared_811_ = v_isSharedCheck_838_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_snapshotTasks_808_);
lean_inc(v_infoState_807_);
lean_inc(v_messages_806_);
lean_inc(v_recordedDeps_805_);
lean_inc(v_cache_804_);
lean_inc(v_traceState_799_);
lean_inc(v_auxDeclNGen_803_);
lean_inc(v_ngen_802_);
lean_inc(v_nextMacroScope_801_);
lean_inc(v_env_800_);
lean_dec(v___x_798_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_838_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
uint64_t v_tid_812_; lean_object* v_traces_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_837_; 
v_tid_812_ = lean_ctor_get_uint64(v_traceState_799_, sizeof(void*)*1);
v_traces_813_ = lean_ctor_get(v_traceState_799_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v_traceState_799_);
if (v_isSharedCheck_837_ == 0)
{
v___x_815_ = v_traceState_799_;
v_isShared_816_ = v_isSharedCheck_837_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_traces_813_);
lean_dec(v_traceState_799_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_837_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; double v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_817_ = lean_box(0);
v___x_818_ = lean_box(0);
v___x_819_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_820_ = 0;
v___x_821_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_822_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_822_, 0, v_cls_785_);
lean_ctor_set(v___x_822_, 1, v___x_818_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
lean_ctor_set_float(v___x_822_, sizeof(void*)*3, v___x_819_);
lean_ctor_set_float(v___x_822_, sizeof(void*)*3 + 8, v___x_819_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*3 + 16, v___x_820_);
v___x_823_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_824_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v_a_794_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
lean_inc(v_ref_792_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_ref_792_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_PersistentArray_push___redArg(v_traces_813_, v___x_825_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_826_);
v___x_828_ = v___x_815_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_826_);
lean_ctor_set_uint64(v_reuseFailAlloc_836_, sizeof(void*)*1, v_tid_812_);
v___x_828_ = v_reuseFailAlloc_836_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; 
if (v_isShared_811_ == 0)
{
lean_ctor_set(v___x_810_, 4, v___x_828_);
v___x_830_ = v___x_810_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_env_800_);
lean_ctor_set(v_reuseFailAlloc_835_, 1, v_nextMacroScope_801_);
lean_ctor_set(v_reuseFailAlloc_835_, 2, v_ngen_802_);
lean_ctor_set(v_reuseFailAlloc_835_, 3, v_auxDeclNGen_803_);
lean_ctor_set(v_reuseFailAlloc_835_, 4, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_835_, 5, v_cache_804_);
lean_ctor_set(v_reuseFailAlloc_835_, 6, v_recordedDeps_805_);
lean_ctor_set(v_reuseFailAlloc_835_, 7, v_messages_806_);
lean_ctor_set(v_reuseFailAlloc_835_, 8, v_infoState_807_);
lean_ctor_set(v_reuseFailAlloc_835_, 9, v_snapshotTasks_808_);
v___x_830_ = v_reuseFailAlloc_835_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_833_; 
v___x_831_ = lean_st_ref_put(v___y_790_, v___x_830_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_817_);
v___x_833_ = v___x_796_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v___x_817_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object* v_cls_840_, lean_object* v_msg_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_840_, v_msg_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_856_ = l_Lean_Name_append(v___x_855_, v___x_854_);
return v___x_856_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object* v_infos_860_, lean_object* v_levels_861_, lean_object* v_as_862_, size_t v_sz_863_, size_t v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
uint8_t v___x_871_; 
v___x_871_ = lean_usize_dec_lt(v_i_864_, v_sz_863_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
lean_dec(v_levels_861_);
lean_dec_ref(v_infos_860_);
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_b_865_);
return v___x_872_;
}
else
{
lean_object* v_a_873_; lean_object* v_toConstantVal_874_; lean_object* v_numParams_875_; lean_object* v_name_876_; lean_object* v_levelParams_877_; lean_object* v_type_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___f_881_; uint8_t v___x_882_; lean_object* v___x_883_; 
v_a_873_ = lean_array_uget_borrowed(v_as_862_, v_i_864_);
v_toConstantVal_874_ = lean_ctor_get(v_a_873_, 0);
v_numParams_875_ = lean_ctor_get(v_a_873_, 1);
v_name_876_ = lean_ctor_get(v_toConstantVal_874_, 0);
v_levelParams_877_ = lean_ctor_get(v_toConstantVal_874_, 1);
v_type_878_ = lean_ctor_get(v_toConstantVal_874_, 2);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = lean_box(0);
lean_inc(v_levels_861_);
lean_inc(v_name_876_);
lean_inc(v_numParams_875_);
lean_inc_ref(v_infos_860_);
v___f_881_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed), 12, 5);
lean_closure_set(v___f_881_, 0, v_infos_860_);
lean_closure_set(v___f_881_, 1, v_numParams_875_);
lean_closure_set(v___f_881_, 2, v___x_879_);
lean_closure_set(v___f_881_, 3, v_name_876_);
lean_closure_set(v___f_881_, 4, v_levels_861_);
v___x_882_ = 0;
lean_inc_ref(v_type_878_);
v___x_883_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_878_, v___f_881_, v___x_882_, v___x_882_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v_toCold_919_; lean_object* v_options_920_; uint8_t v_hasTrace_921_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
v_toCold_919_ = lean_ctor_get(v___y_868_, 0);
v_options_920_ = lean_ctor_get(v_toCold_919_, 2);
v_hasTrace_921_ = lean_ctor_get_uint8(v_options_920_, sizeof(void*)*1);
if (v_hasTrace_921_ == 0)
{
v___y_886_ = v___y_866_;
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
v___y_889_ = v___y_869_;
goto v___jp_885_;
}
else
{
lean_object* v_inheritedTraceOptions_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_inheritedTraceOptions_922_ = lean_ctor_get(v_toCold_919_, 11);
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_924_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_925_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_922_, v_options_920_, v___x_924_);
if (v___x_925_ == 0)
{
v___y_886_ = v___y_866_;
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
v___y_889_ = v___y_869_;
goto v___jp_885_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_926_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
lean_inc(v_a_884_);
v___x_927_ = l_Lean_MessageData_ofExpr(v_a_884_);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_923_, v___x_928_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_dec_ref_known(v___x_929_, 1);
v___y_886_ = v___y_866_;
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
v___y_889_ = v___y_869_;
goto v___jp_885_;
}
else
{
lean_dec(v_a_884_);
lean_dec(v_levels_861_);
lean_dec_ref(v_infos_860_);
return v___x_929_;
}
}
}
v___jp_885_:
{
lean_object* v___x_890_; 
lean_inc(v___y_889_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
lean_inc(v_a_884_);
v___x_890_ = lean_infer_type(v_a_884_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
lean_inc(v_name_876_);
v___x_892_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_876_);
v___x_893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_894_ = l_Lean_Name_append(v___x_892_, v___x_893_);
v___x_895_ = lean_box(0);
lean_inc(v_levelParams_877_);
v___x_896_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_894_, v_levelParams_877_, v_a_891_, v_a_884_, v___x_895_, v___y_889_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_a_897_);
v___x_899_ = l_Lean_addDecl(v___x_898_, v___x_882_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_899_) == 0)
{
size_t v___x_900_; size_t v___x_901_; 
lean_dec_ref_known(v___x_899_, 1);
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_add(v_i_864_, v___x_900_);
v_i_864_ = v___x_901_;
v_b_865_ = v___x_880_;
goto _start;
}
else
{
lean_dec(v_levels_861_);
lean_dec_ref(v_infos_860_);
return v___x_899_;
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_levels_861_);
lean_dec_ref(v_infos_860_);
v_a_903_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_896_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_896_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
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
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec(v_a_884_);
lean_dec(v_levels_861_);
lean_dec_ref(v_infos_860_);
v_a_911_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_890_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_890_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_levels_861_);
lean_dec_ref(v_infos_860_);
v_a_930_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_883_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_883_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object* v_infos_938_, lean_object* v_levels_939_, lean_object* v_as_940_, lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
size_t v_sz_boxed_949_; size_t v_i_boxed_950_; lean_object* v_res_951_; 
v_sz_boxed_949_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_950_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_938_, v_levels_939_, v_as_940_, v_sz_boxed_949_, v_i_boxed_950_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_as_940_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object* v_infos_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_toConstantVal_961_; lean_object* v_levelParams_962_; lean_object* v___x_963_; lean_object* v_levels_964_; lean_object* v___x_965_; size_t v_sz_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___x_958_ = l_Lean_instInhabitedInductiveVal_default;
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = lean_array_get_borrowed(v___x_958_, v_infos_952_, v___x_959_);
v_toConstantVal_961_ = lean_ctor_get(v___x_960_, 0);
v_levelParams_962_ = lean_ctor_get(v_toConstantVal_961_, 1);
v___x_963_ = lean_box(0);
lean_inc(v_levelParams_962_);
v_levels_964_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_962_, v___x_963_);
v___x_965_ = lean_box(0);
v_sz_966_ = lean_array_size(v_infos_952_);
v___x_967_ = ((size_t)0ULL);
lean_inc_ref(v_infos_952_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_952_, v_levels_964_, v_infos_952_, v_sz_966_, v___x_967_, v___x_965_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec_ref(v_infos_952_);
if (lean_obj_tag(v___x_968_) == 0)
{
lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_968_);
if (v_isSharedCheck_975_ == 0)
{
lean_object* v_unused_976_; 
v_unused_976_ = lean_ctor_get(v___x_968_, 0);
lean_dec(v_unused_976_);
v___x_970_ = v___x_968_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_dec(v___x_968_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_965_);
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_965_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
else
{
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object* v_infos_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object* v_00_u03b1_984_, lean_object* v_msg_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object* v_00_u03b1_992_, lean_object* v_msg_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_992_, v_msg_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object* v_inst_1000_, lean_object* v_R_1001_, lean_object* v_a_1002_, lean_object* v_b_1003_, lean_object* v_c_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_1002_, v_b_1003_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object* v_inst_1011_, lean_object* v_R_1012_, lean_object* v_a_1013_, lean_object* v_b_1014_, lean_object* v_c_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_1011_, v_R_1012_, v_a_1013_, v_b_1014_, v_c_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object* v_mvarId_1022_, lean_object* v_val_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_1022_, v_val_1023_, v___y_1025_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object* v_mvarId_1030_, lean_object* v_val_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1030_, v_val_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object* v_00_u03b2_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_1039_, v_x_1040_, v_x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1043_, lean_object* v_x_1044_, size_t v_x_1045_, size_t v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_1044_, v_x_1045_, v_x_1046_, v_x_1047_, v_x_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
size_t v_x_9763__boxed_1056_; size_t v_x_9764__boxed_1057_; lean_object* v_res_1058_; 
v_x_9763__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_x_9764__boxed_1057_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_res_1058_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_1050_, v_x_1051_, v_x_9763__boxed_1056_, v_x_9764__boxed_1057_, v_x_1054_, v_x_1055_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1059_, lean_object* v_n_1060_, lean_object* v_k_1061_, lean_object* v_v_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v_n_1060_, v_k_1061_, v_v_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1064_, size_t v_depth_1065_, lean_object* v_keys_1066_, lean_object* v_vals_1067_, lean_object* v_heq_1068_, lean_object* v_i_1069_, lean_object* v_entries_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_1065_, v_keys_1066_, v_vals_1067_, v_i_1069_, v_entries_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1072_, lean_object* v_depth_1073_, lean_object* v_keys_1074_, lean_object* v_vals_1075_, lean_object* v_heq_1076_, lean_object* v_i_1077_, lean_object* v_entries_1078_){
_start:
{
size_t v_depth_boxed_1079_; lean_object* v_res_1080_; 
v_depth_boxed_1079_ = lean_unbox_usize(v_depth_1073_);
lean_dec(v_depth_1073_);
v_res_1080_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(v_00_u03b2_1072_, v_depth_boxed_1079_, v_keys_1074_, v_vals_1075_, v_heq_1076_, v_i_1077_, v_entries_1078_);
lean_dec_ref(v_vals_1075_);
lean_dec_ref(v_keys_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_x_1082_, v_x_1083_, v_x_1084_, v_x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object* v_e_1087_, lean_object* v___y_1088_){
_start:
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Lean_Expr_hasMVar(v_e_1087_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_e_1087_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; lean_object* v_mctx_1093_; lean_object* v___x_1094_; lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___x_1097_; lean_object* v_cache_1098_; lean_object* v_zetaDeltaFVarIds_1099_; lean_object* v_postponed_1100_; lean_object* v_diag_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1110_; 
v___x_1092_ = lean_st_ref_get(v___y_1088_);
v_mctx_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc_ref(v_mctx_1093_);
lean_dec(v___x_1092_);
v___x_1094_ = l_Lean_instantiateMVarsCore(v_mctx_1093_, v_e_1087_);
v_fst_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_fst_1095_);
v_snd_1096_ = lean_ctor_get(v___x_1094_, 1);
lean_inc(v_snd_1096_);
lean_dec_ref(v___x_1094_);
v___x_1097_ = lean_st_ref_take(v___y_1088_);
v_cache_1098_ = lean_ctor_get(v___x_1097_, 1);
v_zetaDeltaFVarIds_1099_ = lean_ctor_get(v___x_1097_, 2);
v_postponed_1100_ = lean_ctor_get(v___x_1097_, 3);
v_diag_1101_ = lean_ctor_get(v___x_1097_, 4);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1110_ == 0)
{
lean_object* v_unused_1111_; 
v_unused_1111_ = lean_ctor_get(v___x_1097_, 0);
lean_dec(v_unused_1111_);
v___x_1103_ = v___x_1097_;
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_diag_1101_);
lean_inc(v_postponed_1100_);
lean_inc(v_zetaDeltaFVarIds_1099_);
lean_inc(v_cache_1098_);
lean_dec(v___x_1097_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1110_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 0, v_snd_1096_);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_snd_1096_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_cache_1098_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_zetaDeltaFVarIds_1099_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_postponed_1100_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_diag_1101_);
v___x_1106_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_st_ref_put(v___y_1088_, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_fst_1095_);
return v___x_1108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_e_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1112_, v___y_1113_);
lean_dec(v___y_1113_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_e_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1116_, v___y_1120_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_e_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object* v_k_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v_b_1137_, lean_object* v_c_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
lean_inc(v___y_1142_);
lean_inc_ref(v___y_1141_);
lean_inc(v___y_1140_);
lean_inc_ref(v___y_1139_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
v___x_1144_ = lean_apply_9(v_k_1134_, v_b_1137_, v_c_1138_, v___y_1135_, v___y_1136_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, lean_box(0));
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object* v_k_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v_b_1148_, lean_object* v_c_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1145_, v___y_1146_, v___y_1147_, v_b_1148_, v_c_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_type_1156_, lean_object* v_k_1157_, uint8_t v_cleanupAnnotations_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_){
_start:
{
lean_object* v___f_1166_; uint8_t v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_inc(v___y_1160_);
lean_inc_ref(v___y_1159_);
v___f_1166_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1166_, 0, v_k_1157_);
lean_closure_set(v___f_1166_, 1, v___y_1159_);
lean_closure_set(v___f_1166_, 2, v___y_1160_);
v___x_1167_ = 0;
v___x_1168_ = lean_box(0);
v___x_1169_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1167_, v___x_1168_, v_type_1156_, v___f_1166_, v_cleanupAnnotations_1158_, v___x_1167_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
if (lean_obj_tag(v___x_1169_) == 0)
{
return v___x_1169_;
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_type_1178_, lean_object* v_k_1179_, lean_object* v_cleanupAnnotations_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1188_; lean_object* v_res_1189_; 
v_cleanupAnnotations_boxed_1188_ = lean_unbox(v_cleanupAnnotations_1180_);
v_res_1189_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1178_, v_k_1179_, v_cleanupAnnotations_boxed_1188_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_00_u03b1_1190_, lean_object* v_type_1191_, lean_object* v_k_1192_, uint8_t v_cleanupAnnotations_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1191_, v_k_1192_, v_cleanupAnnotations_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_00_u03b1_1202_, lean_object* v_type_1203_, lean_object* v_k_1204_, lean_object* v_cleanupAnnotations_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1213_; lean_object* v_res_1214_; 
v_cleanupAnnotations_boxed_1213_ = lean_unbox(v_cleanupAnnotations_1205_);
v_res_1214_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_1202_, v_type_1203_, v_k_1204_, v_cleanupAnnotations_boxed_1213_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_name_1215_, lean_object* v_levelParams_1216_, lean_object* v_type_1217_, lean_object* v_value_1218_, lean_object* v_hints_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___x_1222_; uint8_t v___y_1224_; lean_object* v_env_1232_; uint8_t v___x_1233_; 
v___x_1222_ = lean_st_ref_get(v___y_1220_);
v_env_1232_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref_n(v_env_1232_, 2);
lean_dec(v___x_1222_);
v___x_1233_ = l_Lean_Environment_hasUnsafe(v_env_1232_, v_type_1217_);
if (v___x_1233_ == 0)
{
uint8_t v___x_1234_; 
v___x_1234_ = l_Lean_Environment_hasUnsafe(v_env_1232_, v_value_1218_);
if (v___x_1234_ == 0)
{
uint8_t v___x_1235_; 
v___x_1235_ = 1;
v___y_1224_ = v___x_1235_;
goto v___jp_1223_;
}
else
{
goto v___jp_1230_;
}
}
else
{
lean_dec_ref(v_env_1232_);
goto v___jp_1230_;
}
v___jp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_inc(v_name_1215_);
v___x_1225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1225_, 0, v_name_1215_);
lean_ctor_set(v___x_1225_, 1, v_levelParams_1216_);
lean_ctor_set(v___x_1225_, 2, v_type_1217_);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1227_, 0, v_name_1215_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1228_, 0, v___x_1225_);
lean_ctor_set(v___x_1228_, 1, v_value_1218_);
lean_ctor_set(v___x_1228_, 2, v_hints_1219_);
lean_ctor_set(v___x_1228_, 3, v___x_1227_);
lean_ctor_set_uint8(v___x_1228_, sizeof(void*)*4, v___y_1224_);
v___x_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
return v___x_1229_;
}
v___jp_1230_:
{
uint8_t v___x_1231_; 
v___x_1231_ = 0;
v___y_1224_ = v___x_1231_;
goto v___jp_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1236_, lean_object* v_levelParams_1237_, lean_object* v_type_1238_, lean_object* v_value_1239_, lean_object* v_hints_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1236_, v_levelParams_1237_, v_type_1238_, v_value_1239_, v_hints_1240_, v___y_1241_);
lean_dec(v___y_1241_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1244_, lean_object* v_levelParams_1245_, lean_object* v_type_1246_, lean_object* v_value_1247_, lean_object* v_hints_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1244_, v_levelParams_1245_, v_type_1246_, v_value_1247_, v_hints_1248_, v___y_1254_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1257_, lean_object* v_levelParams_1258_, lean_object* v_type_1259_, lean_object* v_value_1260_, lean_object* v_hints_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1257_, v_levelParams_1258_, v_type_1259_, v_value_1260_, v_hints_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1270_, lean_object* v_maxFVars_x3f_1271_, lean_object* v_k_1272_, uint8_t v_cleanupAnnotations_1273_, uint8_t v_whnfType_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___f_1282_; lean_object* v___x_1283_; 
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1282_, 0, v_k_1272_);
lean_closure_set(v___f_1282_, 1, v___y_1275_);
lean_closure_set(v___f_1282_, 2, v___y_1276_);
v___x_1283_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1270_, v_maxFVars_x3f_1271_, v___f_1282_, v_cleanupAnnotations_1273_, v_whnfType_1274_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1283_) == 0)
{
return v___x_1283_;
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1292_, lean_object* v_maxFVars_x3f_1293_, lean_object* v_k_1294_, lean_object* v_cleanupAnnotations_1295_, lean_object* v_whnfType_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1304_; uint8_t v_whnfType_boxed_1305_; lean_object* v_res_1306_; 
v_cleanupAnnotations_boxed_1304_ = lean_unbox(v_cleanupAnnotations_1295_);
v_whnfType_boxed_1305_ = lean_unbox(v_whnfType_1296_);
v_res_1306_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1292_, v_maxFVars_x3f_1293_, v_k_1294_, v_cleanupAnnotations_boxed_1304_, v_whnfType_boxed_1305_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1307_, lean_object* v_type_1308_, lean_object* v_maxFVars_x3f_1309_, lean_object* v_k_1310_, uint8_t v_cleanupAnnotations_1311_, uint8_t v_whnfType_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1308_, v_maxFVars_x3f_1309_, v_k_1310_, v_cleanupAnnotations_1311_, v_whnfType_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1321_, lean_object* v_type_1322_, lean_object* v_maxFVars_x3f_1323_, lean_object* v_k_1324_, lean_object* v_cleanupAnnotations_1325_, lean_object* v_whnfType_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1334_; uint8_t v_whnfType_boxed_1335_; lean_object* v_res_1336_; 
v_cleanupAnnotations_boxed_1334_ = lean_unbox(v_cleanupAnnotations_1325_);
v_whnfType_boxed_1335_ = lean_unbox(v_whnfType_1326_);
v_res_1336_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1321_, v_type_1322_, v_maxFVars_x3f_1323_, v_k_1324_, v_cleanupAnnotations_boxed_1334_, v_whnfType_boxed_1335_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_toCold_1345_; lean_object* v_options_1346_; uint8_t v_hasTrace_1347_; 
v_toCold_1345_ = lean_ctor_get(v___y_1342_, 0);
v_options_1346_ = lean_ctor_get(v_toCold_1345_, 2);
v_hasTrace_1347_ = lean_ctor_get_uint8(v_options_1346_, sizeof(void*)*1);
if (v_hasTrace_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_cls_1337_);
v___x_1348_ = lean_box(v_hasTrace_1347_);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
else
{
lean_object* v_inheritedTraceOptions_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_inheritedTraceOptions_1350_ = lean_ctor_get(v_toCold_1345_, 11);
v___x_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1352_ = l_Lean_Name_append(v___x_1351_, v_cls_1337_);
v___x_1353_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1350_, v_options_1346_, v___x_1352_);
lean_dec(v___x_1352_);
v___x_1354_ = lean_box(v___x_1353_);
v___x_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object* v_cls_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_mvarId_1365_, lean_object* v_val_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; lean_object* v_mctx_1370_; lean_object* v_cache_1371_; lean_object* v_zetaDeltaFVarIds_1372_; lean_object* v_postponed_1373_; lean_object* v_diag_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1404_; 
v___x_1369_ = lean_st_ref_take(v___y_1367_);
v_mctx_1370_ = lean_ctor_get(v___x_1369_, 0);
v_cache_1371_ = lean_ctor_get(v___x_1369_, 1);
v_zetaDeltaFVarIds_1372_ = lean_ctor_get(v___x_1369_, 2);
v_postponed_1373_ = lean_ctor_get(v___x_1369_, 3);
v_diag_1374_ = lean_ctor_get(v___x_1369_, 4);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1376_ = v___x_1369_;
v_isShared_1377_ = v_isSharedCheck_1404_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_diag_1374_);
lean_inc(v_postponed_1373_);
lean_inc(v_zetaDeltaFVarIds_1372_);
lean_inc(v_cache_1371_);
lean_inc(v_mctx_1370_);
lean_dec(v___x_1369_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1404_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_depth_1378_; lean_object* v_levelAssignDepth_1379_; lean_object* v_lmvarCounter_1380_; lean_object* v_mvarCounter_1381_; lean_object* v_lDecls_1382_; lean_object* v_decls_1383_; lean_object* v_userNames_1384_; lean_object* v_lAssignment_1385_; lean_object* v_eAssignment_1386_; lean_object* v_dAssignment_1387_; lean_object* v_instanceTypedMVars_1388_; lean_object* v_synthNormMemo_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1403_; 
v_depth_1378_ = lean_ctor_get(v_mctx_1370_, 0);
v_levelAssignDepth_1379_ = lean_ctor_get(v_mctx_1370_, 1);
v_lmvarCounter_1380_ = lean_ctor_get(v_mctx_1370_, 2);
v_mvarCounter_1381_ = lean_ctor_get(v_mctx_1370_, 3);
v_lDecls_1382_ = lean_ctor_get(v_mctx_1370_, 4);
v_decls_1383_ = lean_ctor_get(v_mctx_1370_, 5);
v_userNames_1384_ = lean_ctor_get(v_mctx_1370_, 6);
v_lAssignment_1385_ = lean_ctor_get(v_mctx_1370_, 7);
v_eAssignment_1386_ = lean_ctor_get(v_mctx_1370_, 8);
v_dAssignment_1387_ = lean_ctor_get(v_mctx_1370_, 9);
v_instanceTypedMVars_1388_ = lean_ctor_get(v_mctx_1370_, 10);
v_synthNormMemo_1389_ = lean_ctor_get(v_mctx_1370_, 11);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_mctx_1370_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1391_ = v_mctx_1370_;
v_isShared_1392_ = v_isSharedCheck_1403_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_synthNormMemo_1389_);
lean_inc(v_instanceTypedMVars_1388_);
lean_inc(v_dAssignment_1387_);
lean_inc(v_eAssignment_1386_);
lean_inc(v_lAssignment_1385_);
lean_inc(v_userNames_1384_);
lean_inc(v_decls_1383_);
lean_inc(v_lDecls_1382_);
lean_inc(v_mvarCounter_1381_);
lean_inc(v_lmvarCounter_1380_);
lean_inc(v_levelAssignDepth_1379_);
lean_inc(v_depth_1378_);
lean_dec(v_mctx_1370_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1403_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1386_, v_mvarId_1365_, v_val_1366_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 8, v___x_1394_);
v___x_1396_ = v___x_1391_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_depth_1378_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_levelAssignDepth_1379_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_lmvarCounter_1380_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_mvarCounter_1381_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_lDecls_1382_);
lean_ctor_set(v_reuseFailAlloc_1402_, 5, v_decls_1383_);
lean_ctor_set(v_reuseFailAlloc_1402_, 6, v_userNames_1384_);
lean_ctor_set(v_reuseFailAlloc_1402_, 7, v_lAssignment_1385_);
lean_ctor_set(v_reuseFailAlloc_1402_, 8, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1402_, 9, v_dAssignment_1387_);
lean_ctor_set(v_reuseFailAlloc_1402_, 10, v_instanceTypedMVars_1388_);
lean_ctor_set(v_reuseFailAlloc_1402_, 11, v_synthNormMemo_1389_);
v___x_1396_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1396_);
v___x_1398_ = v___x_1376_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_cache_1371_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_zetaDeltaFVarIds_1372_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_postponed_1373_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_diag_1374_);
v___x_1398_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_st_ref_put(v___y_1367_, v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1393_);
return v___x_1400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_mvarId_1405_, lean_object* v_val_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1405_, v_val_1406_, v___y_1407_);
lean_dec(v___y_1407_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_cls_1410_, lean_object* v_msg_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v_ref_1417_; lean_object* v___x_1418_; lean_object* v_a_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1464_; 
v_ref_1417_ = lean_ctor_get(v___y_1414_, 2);
v___x_1418_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1421_ = v___x_1418_;
v_isShared_1422_ = v_isSharedCheck_1464_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_a_1419_);
lean_dec(v___x_1418_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1464_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v_traceState_1424_; lean_object* v_env_1425_; lean_object* v_nextMacroScope_1426_; lean_object* v_ngen_1427_; lean_object* v_auxDeclNGen_1428_; lean_object* v_cache_1429_; lean_object* v_recordedDeps_1430_; lean_object* v_messages_1431_; lean_object* v_infoState_1432_; lean_object* v_snapshotTasks_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1463_; 
v___x_1423_ = lean_st_ref_take(v___y_1415_);
v_traceState_1424_ = lean_ctor_get(v___x_1423_, 4);
v_env_1425_ = lean_ctor_get(v___x_1423_, 0);
v_nextMacroScope_1426_ = lean_ctor_get(v___x_1423_, 1);
v_ngen_1427_ = lean_ctor_get(v___x_1423_, 2);
v_auxDeclNGen_1428_ = lean_ctor_get(v___x_1423_, 3);
v_cache_1429_ = lean_ctor_get(v___x_1423_, 5);
v_recordedDeps_1430_ = lean_ctor_get(v___x_1423_, 6);
v_messages_1431_ = lean_ctor_get(v___x_1423_, 7);
v_infoState_1432_ = lean_ctor_get(v___x_1423_, 8);
v_snapshotTasks_1433_ = lean_ctor_get(v___x_1423_, 9);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1435_ = v___x_1423_;
v_isShared_1436_ = v_isSharedCheck_1463_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snapshotTasks_1433_);
lean_inc(v_infoState_1432_);
lean_inc(v_messages_1431_);
lean_inc(v_recordedDeps_1430_);
lean_inc(v_cache_1429_);
lean_inc(v_traceState_1424_);
lean_inc(v_auxDeclNGen_1428_);
lean_inc(v_ngen_1427_);
lean_inc(v_nextMacroScope_1426_);
lean_inc(v_env_1425_);
lean_dec(v___x_1423_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1463_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
uint64_t v_tid_1437_; lean_object* v_traces_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1462_; 
v_tid_1437_ = lean_ctor_get_uint64(v_traceState_1424_, sizeof(void*)*1);
v_traces_1438_ = lean_ctor_get(v_traceState_1424_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_traceState_1424_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1440_ = v_traceState_1424_;
v_isShared_1441_ = v_isSharedCheck_1462_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_traces_1438_);
lean_dec(v_traceState_1424_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1462_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1443_; double v___x_1444_; uint8_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_box(0);
v___x_1444_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_1445_ = 0;
v___x_1446_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_1447_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1447_, 0, v_cls_1410_);
lean_ctor_set(v___x_1447_, 1, v___x_1443_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
lean_ctor_set_float(v___x_1447_, sizeof(void*)*3, v___x_1444_);
lean_ctor_set_float(v___x_1447_, sizeof(void*)*3 + 8, v___x_1444_);
lean_ctor_set_uint8(v___x_1447_, sizeof(void*)*3 + 16, v___x_1445_);
v___x_1448_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_1449_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1447_);
lean_ctor_set(v___x_1449_, 1, v_a_1419_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
lean_inc(v_ref_1417_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_ref_1417_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = l_Lean_PersistentArray_push___redArg(v_traces_1438_, v___x_1450_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1451_);
v___x_1453_ = v___x_1440_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1451_);
lean_ctor_set_uint64(v_reuseFailAlloc_1461_, sizeof(void*)*1, v_tid_1437_);
v___x_1453_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 4, v___x_1453_);
v___x_1455_ = v___x_1435_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v_env_1425_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_nextMacroScope_1426_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_ngen_1427_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_auxDeclNGen_1428_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1460_, 5, v_cache_1429_);
lean_ctor_set(v_reuseFailAlloc_1460_, 6, v_recordedDeps_1430_);
lean_ctor_set(v_reuseFailAlloc_1460_, 7, v_messages_1431_);
lean_ctor_set(v_reuseFailAlloc_1460_, 8, v_infoState_1432_);
lean_ctor_set(v_reuseFailAlloc_1460_, 9, v_snapshotTasks_1433_);
v___x_1455_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1456_ = lean_st_ref_put(v___y_1415_, v___x_1455_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 0, v___x_1442_);
v___x_1458_ = v___x_1421_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1442_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_cls_1465_, lean_object* v_msg_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1465_, v_msg_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
return v_res_1472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1473_; lean_object* v_dummy_1474_; 
v___x_1473_ = lean_box(0);
v_dummy_1474_ = l_Lean_Expr_sort___override(v___x_1473_);
return v_dummy_1474_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1476_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1));
v___x_1477_ = l_Lean_stringToMessageData(v___x_1476_);
return v___x_1477_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3));
v___x_1480_ = l_Lean_stringToMessageData(v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v_numParams_1481_, lean_object* v___x_1482_, lean_object* v_name_1483_, lean_object* v___x_1484_, lean_object* v___x_1485_, lean_object* v_name_1486_, lean_object* v___x_1487_, lean_object* v_cls_1488_, lean_object* v_fields_1489_, lean_object* v_bodyExpr_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_toCold_1498_; lean_object* v_options_1499_; lean_object* v_inheritedTraceOptions_1500_; uint8_t v_hasTrace_1501_; lean_object* v_nargs_1502_; lean_object* v_dummy_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; 
v_toCold_1498_ = lean_ctor_get(v___y_1495_, 0);
v_options_1499_ = lean_ctor_get(v_toCold_1498_, 2);
v_inheritedTraceOptions_1500_ = lean_ctor_get(v_toCold_1498_, 11);
v_hasTrace_1501_ = lean_ctor_get_uint8(v_options_1499_, sizeof(void*)*1);
v_nargs_1502_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1490_);
v_dummy_1503_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
lean_inc(v_nargs_1502_);
v___x_1504_ = lean_mk_array(v_nargs_1502_, v_dummy_1503_);
v___x_1505_ = lean_unsigned_to_nat(1u);
v___x_1506_ = lean_nat_sub(v_nargs_1502_, v___x_1505_);
lean_dec(v_nargs_1502_);
v___x_1507_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1490_, v___x_1504_, v___x_1506_);
v___x_1508_ = lean_array_get_size(v___x_1507_);
v___x_1509_ = lean_nat_add(v_numParams_1481_, v___x_1482_);
v___x_1510_ = l_Array_toSubarray___redArg(v___x_1507_, v___x_1509_, v___x_1508_);
v___x_1511_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1483_);
lean_inc(v___x_1484_);
lean_inc(v___x_1511_);
v___x_1512_ = l_Lean_mkConst(v___x_1511_, v___x_1484_);
v___x_1513_ = l_Lean_mkAppN(v___x_1512_, v___x_1485_);
v___x_1514_ = l_Subarray_copy___redArg(v___x_1510_);
v___x_1515_ = l_Lean_mkAppN(v___x_1513_, v___x_1514_);
lean_dec_ref(v___x_1514_);
if (v_hasTrace_1501_ == 0)
{
lean_dec(v_cls_1488_);
v___y_1517_ = v___y_1491_;
v___y_1518_ = v___y_1492_;
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
v___y_1521_ = v___y_1495_;
v___y_1522_ = v___y_1496_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
lean_inc(v_cls_1488_);
v___x_1572_ = l_Lean_Name_append(v___x_1571_, v_cls_1488_);
v___x_1573_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1500_, v_options_1499_, v___x_1572_);
lean_dec(v___x_1572_);
if (v___x_1573_ == 0)
{
lean_dec(v_cls_1488_);
v___y_1517_ = v___y_1491_;
v___y_1518_ = v___y_1492_;
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
v___y_1521_ = v___y_1495_;
v___y_1522_ = v___y_1496_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1574_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
lean_inc(v_name_1486_);
v___x_1575_ = l_Lean_MessageData_ofName(v_name_1486_);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
lean_inc_ref(v___x_1515_);
v___x_1579_ = l_Lean_MessageData_ofExpr(v___x_1515_);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
v___x_1581_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1488_, v___x_1580_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_dec_ref_known(v___x_1581_, 1);
v___y_1517_ = v___y_1491_;
v___y_1518_ = v___y_1492_;
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
v___y_1521_ = v___y_1495_;
v___y_1522_ = v___y_1496_;
goto v___jp_1516_;
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v___x_1515_);
lean_dec(v___x_1511_);
lean_dec(v_name_1486_);
lean_dec(v___x_1484_);
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1581_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
v___jp_1516_:
{
lean_object* v___x_1523_; uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1515_);
v___x_1524_ = 0;
v___x_1525_ = lean_box(0);
v___x_1526_ = l_Lean_Meta_mkFreshExprMVar(v___x_1523_, v___x_1524_, v___x_1525_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = l_Lean_Expr_mvarId_x21(v_a_1527_);
v___x_1529_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1530_ = l_Lean_Name_append(v___x_1511_, v___x_1529_);
lean_inc(v___x_1484_);
v___x_1531_ = l_Lean_mkConst(v___x_1530_, v___x_1484_);
v___x_1532_ = l_Lean_mkAppN(v___x_1531_, v___x_1485_);
lean_inc(v___x_1528_);
v___x_1533_ = l_Lean_MVarId_getType(v___x_1528_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; uint8_t v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = 0;
v___x_1536_ = 1;
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1528_);
v___x_1538_ = l_Lean_MVarId_rewrite(v___x_1528_, v_a_1534_, v___x_1532_, v___x_1535_, v___x_1537_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v_eNew_1540_; lean_object* v_eqProof_1541_; lean_object* v___x_1542_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
v_eNew_1540_ = lean_ctor_get(v_a_1539_, 0);
lean_inc_ref(v_eNew_1540_);
v_eqProof_1541_ = lean_ctor_get(v_a_1539_, 1);
lean_inc_ref(v_eqProof_1541_);
lean_dec(v_a_1539_);
v___x_1542_ = l_Lean_MVarId_replaceTargetEq(v___x_1528_, v_eNew_1540_, v_eqProof_1541_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v_a_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = l_Lean_mkConst(v_name_1486_, v___x_1484_);
v___x_1545_ = l_Lean_mkAppN(v___x_1544_, v___x_1485_);
v___x_1546_ = l_Lean_mkAppN(v___x_1545_, v___x_1487_);
v___x_1547_ = l_Lean_mkAppN(v___x_1546_, v_fields_1489_);
v___x_1548_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_1543_, v___x_1547_, v___y_1520_);
lean_dec_ref(v___x_1548_);
v___x_1549_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1527_, v___y_1520_);
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = 1;
v___x_1552_ = l_Lean_Meta_mkLambdaFVars(v_fields_1489_, v_a_1550_, v___x_1535_, v___x_1536_, v___x_1535_, v___x_1536_, v___x_1551_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = l_Lean_Meta_mkLambdaFVars(v___x_1485_, v_a_1553_, v___x_1535_, v___x_1536_, v___x_1535_, v___x_1536_, v___x_1551_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1554_;
}
else
{
return v___x_1552_;
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec(v_a_1527_);
lean_dec(v_name_1486_);
lean_dec(v___x_1484_);
v_a_1555_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1542_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1542_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1570_; 
lean_dec(v___x_1528_);
lean_dec(v_a_1527_);
lean_dec(v_name_1486_);
lean_dec(v___x_1484_);
v_a_1563_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1565_ = v___x_1538_;
v_isShared_1566_ = v_isSharedCheck_1570_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_a_1563_);
lean_dec(v___x_1538_);
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
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_a_1563_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
else
{
lean_dec_ref(v___x_1532_);
lean_dec(v___x_1528_);
lean_dec(v_a_1527_);
lean_dec(v_name_1486_);
lean_dec(v___x_1484_);
return v___x_1533_;
}
}
else
{
lean_dec(v___x_1511_);
lean_dec(v_name_1486_);
lean_dec(v___x_1484_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_1590_ = _args[0];
lean_object* v___x_1591_ = _args[1];
lean_object* v_name_1592_ = _args[2];
lean_object* v___x_1593_ = _args[3];
lean_object* v___x_1594_ = _args[4];
lean_object* v_name_1595_ = _args[5];
lean_object* v___x_1596_ = _args[6];
lean_object* v_cls_1597_ = _args[7];
lean_object* v_fields_1598_ = _args[8];
lean_object* v_bodyExpr_1599_ = _args[9];
lean_object* v___y_1600_ = _args[10];
lean_object* v___y_1601_ = _args[11];
lean_object* v___y_1602_ = _args[12];
lean_object* v___y_1603_ = _args[13];
lean_object* v___y_1604_ = _args[14];
lean_object* v___y_1605_ = _args[15];
lean_object* v___y_1606_ = _args[16];
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1590_, v___x_1591_, v_name_1592_, v___x_1593_, v___x_1594_, v_name_1595_, v___x_1596_, v_cls_1597_, v_fields_1598_, v_bodyExpr_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v_fields_1598_);
lean_dec_ref(v___x_1596_);
lean_dec_ref(v___x_1594_);
lean_dec(v___x_1591_);
lean_dec(v_numParams_1590_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1608_, size_t v_sz_1609_, size_t v_i_1610_, lean_object* v_bs_1611_){
_start:
{
uint8_t v___x_1612_; 
v___x_1612_ = lean_usize_dec_lt(v_i_1610_, v_sz_1609_);
if (v___x_1612_ == 0)
{
return v_bs_1611_;
}
else
{
lean_object* v_v_1613_; lean_object* v___x_1614_; lean_object* v_bs_x27_1615_; lean_object* v___x_1616_; size_t v___x_1617_; size_t v___x_1618_; lean_object* v___x_1619_; 
v_v_1613_ = lean_array_uget(v_bs_1611_, v_i_1610_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v_bs_x27_1615_ = lean_array_uset(v_bs_1611_, v_i_1610_, v___x_1614_);
v___x_1616_ = l_Lean_mkAppN(v_v_1613_, v___x_1608_);
v___x_1617_ = ((size_t)1ULL);
v___x_1618_ = lean_usize_add(v_i_1610_, v___x_1617_);
v___x_1619_ = lean_array_uset(v_bs_x27_1615_, v_i_1610_, v___x_1616_);
v_i_1610_ = v___x_1618_;
v_bs_1611_ = v___x_1619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1621_, lean_object* v_sz_1622_, lean_object* v_i_1623_, lean_object* v_bs_1624_){
_start:
{
size_t v_sz_boxed_1625_; size_t v_i_boxed_1626_; lean_object* v_res_1627_; 
v_sz_boxed_1625_ = lean_unbox_usize(v_sz_1622_);
lean_dec(v_sz_1622_);
v_i_boxed_1626_ = lean_unbox_usize(v_i_1623_);
lean_dec(v_i_1623_);
v_res_1627_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1621_, v_sz_boxed_1625_, v_i_boxed_1626_, v_bs_1624_);
lean_dec_ref(v___x_1621_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1628_, size_t v_sz_1629_, size_t v_i_1630_, lean_object* v_bs_1631_){
_start:
{
uint8_t v___x_1632_; 
v___x_1632_ = lean_usize_dec_lt(v_i_1630_, v_sz_1629_);
if (v___x_1632_ == 0)
{
lean_dec(v___x_1628_);
return v_bs_1631_;
}
else
{
lean_object* v_v_1633_; lean_object* v___x_1634_; lean_object* v_bs_x27_1635_; lean_object* v___x_1636_; size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; 
v_v_1633_ = lean_array_uget(v_bs_1631_, v_i_1630_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v_bs_x27_1635_ = lean_array_uset(v_bs_1631_, v_i_1630_, v___x_1634_);
lean_inc(v___x_1628_);
v___x_1636_ = l_Lean_mkConst(v_v_1633_, v___x_1628_);
v___x_1637_ = ((size_t)1ULL);
v___x_1638_ = lean_usize_add(v_i_1630_, v___x_1637_);
v___x_1639_ = lean_array_uset(v_bs_x27_1635_, v_i_1630_, v___x_1636_);
v_i_1630_ = v___x_1638_;
v_bs_1631_ = v___x_1639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1641_, lean_object* v_sz_1642_, lean_object* v_i_1643_, lean_object* v_bs_1644_){
_start:
{
size_t v_sz_boxed_1645_; size_t v_i_boxed_1646_; lean_object* v_res_1647_; 
v_sz_boxed_1645_ = lean_unbox_usize(v_sz_1642_);
lean_dec(v_sz_1642_);
v_i_boxed_1646_ = lean_unbox_usize(v_i_1643_);
lean_dec(v_i_1643_);
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1641_, v_sz_boxed_1645_, v_i_boxed_1646_, v_bs_1644_);
return v_res_1647_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0));
v___x_1650_ = l_Lean_stringToMessageData(v___x_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object* v___x_1651_, lean_object* v_numParams_1652_, lean_object* v___x_1653_, lean_object* v___x_1654_, size_t v___x_1655_, lean_object* v___x_1656_, lean_object* v_name_1657_, lean_object* v_name_1658_, lean_object* v_cls_1659_, lean_object* v_levelParams_1660_, lean_object* v_ctorSyntax_1661_, lean_object* v___f_1662_, lean_object* v_args_1663_, lean_object* v_body_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; size_t v_sz_1675_; lean_object* v___x_1676_; size_t v_sz_1677_; lean_object* v___x_1678_; lean_object* v___f_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; lean_object* v___x_1683_; 
lean_inc_n(v_numParams_1652_, 2);
v___x_1672_ = l_Array_extract___redArg(v_args_1663_, v___x_1651_, v_numParams_1652_);
v___x_1673_ = lean_array_get_size(v_args_1663_);
v___x_1674_ = l_Array_toSubarray___redArg(v_args_1663_, v_numParams_1652_, v___x_1673_);
v_sz_1675_ = lean_array_size(v___x_1653_);
lean_inc(v___x_1654_);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1654_, v_sz_1675_, v___x_1655_, v___x_1653_);
v_sz_1677_ = lean_array_size(v___x_1676_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1672_, v_sz_1677_, v___x_1655_, v___x_1676_);
lean_inc(v_cls_1659_);
lean_inc_ref(v___x_1678_);
lean_inc(v_name_1658_);
v___f_1679_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1679_, 0, v_numParams_1652_);
lean_closure_set(v___f_1679_, 1, v___x_1656_);
lean_closure_set(v___f_1679_, 2, v_name_1657_);
lean_closure_set(v___f_1679_, 3, v___x_1654_);
lean_closure_set(v___f_1679_, 4, v___x_1672_);
lean_closure_set(v___f_1679_, 5, v_name_1658_);
lean_closure_set(v___f_1679_, 6, v___x_1678_);
lean_closure_set(v___f_1679_, 7, v_cls_1659_);
v___x_1680_ = l_Subarray_copy___redArg(v___x_1674_);
v___x_1681_ = l_Lean_Expr_replaceFVars(v_body_1664_, v___x_1680_, v___x_1678_);
lean_dec_ref(v___x_1678_);
lean_dec_ref(v___x_1680_);
v___x_1682_ = 0;
v___x_1683_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_1681_, v___f_1679_, v___x_1682_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc_n(v_a_1684_, 2);
lean_dec_ref_known(v___x_1683_, 1);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
v___x_1685_ = lean_infer_type(v_a_1684_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___x_1710_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
v___x_1710_ = lean_apply_7(v___f_1662_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, lean_box(0));
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; uint8_t v___x_1712_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_a_1711_);
lean_dec_ref_known(v___x_1710_, 1);
v___x_1712_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
if (v___x_1712_ == 0)
{
lean_dec(v_cls_1659_);
v___y_1688_ = v___y_1665_;
v___y_1689_ = v___y_1666_;
v___y_1690_ = v___y_1667_;
v___y_1691_ = v___y_1668_;
v___y_1692_ = v___y_1669_;
v___y_1693_ = v___y_1670_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1713_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
lean_inc(v_a_1686_);
v___x_1714_ = l_Lean_MessageData_ofExpr(v_a_1686_);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1659_, v___x_1715_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_dec_ref_known(v___x_1716_, 1);
v___y_1688_ = v___y_1665_;
v___y_1689_ = v___y_1666_;
v___y_1690_ = v___y_1667_;
v___y_1691_ = v___y_1668_;
v___y_1692_ = v___y_1669_;
v___y_1693_ = v___y_1670_;
goto v___jp_1687_;
}
else
{
lean_dec(v_a_1686_);
lean_dec(v_a_1684_);
lean_dec(v_ctorSyntax_1661_);
lean_dec(v_levelParams_1660_);
lean_dec(v_name_1658_);
return v___x_1716_;
}
}
}
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec(v_a_1686_);
lean_dec(v_a_1684_);
lean_dec(v_ctorSyntax_1661_);
lean_dec(v_levelParams_1660_);
lean_dec(v_cls_1659_);
lean_dec(v_name_1658_);
v_a_1717_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1710_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1710_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
v___jp_1687_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1709_; 
v___x_1694_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1658_);
v___x_1695_ = lean_box(0);
lean_inc(v_a_1684_);
v___x_1696_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1694_, v_levelParams_1660_, v_a_1686_, v_a_1684_, v___x_1695_, v___y_1693_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1709_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1709_ == 0)
{
v___x_1699_ = v___x_1696_;
v_isShared_1700_ = v_isSharedCheck_1709_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1696_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1709_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set_tag(v___x_1699_, 1);
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_addDecl(v___x_1702_, v___x_1682_, v___y_1692_, v___y_1693_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; lean_object* v___x_1707_; 
lean_dec_ref_known(v___x_1703_, 1);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_box(0);
v___x_1706_ = 1;
v___x_1707_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1661_, v_a_1684_, v___x_1704_, v___x_1704_, v___x_1705_, v___x_1706_, v___x_1682_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1707_;
}
else
{
lean_dec(v_a_1684_);
lean_dec(v_ctorSyntax_1661_);
return v___x_1703_;
}
}
}
}
}
else
{
lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1732_; 
lean_dec(v_a_1684_);
lean_dec_ref(v___f_1662_);
lean_dec(v_ctorSyntax_1661_);
lean_dec(v_levelParams_1660_);
lean_dec(v_cls_1659_);
lean_dec(v_name_1658_);
v_a_1725_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1727_ = v___x_1685_;
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1685_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1732_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
return v___x_1730_;
}
}
}
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec_ref(v___f_1662_);
lean_dec(v_ctorSyntax_1661_);
lean_dec(v_levelParams_1660_);
lean_dec(v_cls_1659_);
lean_dec(v_name_1658_);
v_a_1733_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1683_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1683_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object** _args){
lean_object* v___x_1741_ = _args[0];
lean_object* v_numParams_1742_ = _args[1];
lean_object* v___x_1743_ = _args[2];
lean_object* v___x_1744_ = _args[3];
lean_object* v___x_1745_ = _args[4];
lean_object* v___x_1746_ = _args[5];
lean_object* v_name_1747_ = _args[6];
lean_object* v_name_1748_ = _args[7];
lean_object* v_cls_1749_ = _args[8];
lean_object* v_levelParams_1750_ = _args[9];
lean_object* v_ctorSyntax_1751_ = _args[10];
lean_object* v___f_1752_ = _args[11];
lean_object* v_args_1753_ = _args[12];
lean_object* v_body_1754_ = _args[13];
lean_object* v___y_1755_ = _args[14];
lean_object* v___y_1756_ = _args[15];
lean_object* v___y_1757_ = _args[16];
lean_object* v___y_1758_ = _args[17];
lean_object* v___y_1759_ = _args[18];
lean_object* v___y_1760_ = _args[19];
lean_object* v___y_1761_ = _args[20];
_start:
{
size_t v___x_8909__boxed_1762_; lean_object* v_res_1763_; 
v___x_8909__boxed_1762_ = lean_unbox_usize(v___x_1745_);
lean_dec(v___x_1745_);
v_res_1763_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1741_, v_numParams_1742_, v___x_1743_, v___x_1744_, v___x_8909__boxed_1762_, v___x_1746_, v_name_1747_, v_name_1748_, v_cls_1749_, v_levelParams_1750_, v_ctorSyntax_1751_, v___f_1752_, v_args_1753_, v_body_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v_body_1754_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1764_, size_t v_i_1765_, lean_object* v_bs_1766_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_lt(v_i_1765_, v_sz_1764_);
if (v___x_1767_ == 0)
{
return v_bs_1766_;
}
else
{
lean_object* v_v_1768_; lean_object* v_toConstantVal_1769_; lean_object* v_name_1770_; lean_object* v___x_1771_; lean_object* v_bs_x27_1772_; lean_object* v___x_1773_; size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v_v_1768_ = lean_array_uget_borrowed(v_bs_1766_, v_i_1765_);
v_toConstantVal_1769_ = lean_ctor_get(v_v_1768_, 0);
v_name_1770_ = lean_ctor_get(v_toConstantVal_1769_, 0);
lean_inc(v_name_1770_);
v___x_1771_ = lean_unsigned_to_nat(0u);
v_bs_x27_1772_ = lean_array_uset(v_bs_1766_, v_i_1765_, v___x_1771_);
v___x_1773_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1770_);
v___x_1774_ = ((size_t)1ULL);
v___x_1775_ = lean_usize_add(v_i_1765_, v___x_1774_);
v___x_1776_ = lean_array_uset(v_bs_x27_1772_, v_i_1765_, v___x_1773_);
v_i_1765_ = v___x_1775_;
v_bs_1766_ = v___x_1776_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1778_, lean_object* v_i_1779_, lean_object* v_bs_1780_){
_start:
{
size_t v_sz_boxed_1781_; size_t v_i_boxed_1782_; lean_object* v_res_1783_; 
v_sz_boxed_1781_ = lean_unbox_usize(v_sz_1778_);
lean_dec(v_sz_1778_);
v_i_boxed_1782_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1781_, v_i_boxed_1782_, v_bs_1780_);
return v_res_1783_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1791_, lean_object* v_ctorSyntax_1792_, lean_object* v_numParams_1793_, lean_object* v_name_1794_, lean_object* v_ctor_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v_cls_1804_; lean_object* v___f_1805_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___x_1833_; lean_object* v_a_1834_; uint8_t v___x_1835_; 
v___x_1803_ = l_Lean_instInhabitedInductiveVal_default;
v_cls_1804_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___f_1805_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1833_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1804_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v___x_1835_ = lean_unbox(v_a_1834_);
lean_dec(v_a_1834_);
if (v___x_1835_ == 0)
{
v___y_1807_ = v_a_1796_;
v___y_1808_ = v_a_1797_;
v___y_1809_ = v_a_1798_;
v___y_1810_ = v_a_1799_;
v___y_1811_ = v_a_1800_;
v___y_1812_ = v_a_1801_;
goto v___jp_1806_;
}
else
{
lean_object* v_toConstantVal_1836_; lean_object* v_name_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_toConstantVal_1836_ = lean_ctor_get(v_ctor_1795_, 0);
v_name_1837_ = lean_ctor_get(v_toConstantVal_1836_, 0);
v___x_1838_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
lean_inc(v_name_1837_);
v___x_1839_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1837_);
v___x_1840_ = l_Lean_MessageData_ofName(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1838_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1804_, v___x_1841_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_dec_ref_known(v___x_1842_, 1);
v___y_1807_ = v_a_1796_;
v___y_1808_ = v_a_1797_;
v___y_1809_ = v_a_1798_;
v___y_1810_ = v_a_1799_;
v___y_1811_ = v_a_1800_;
v___y_1812_ = v_a_1801_;
goto v___jp_1806_;
}
else
{
lean_dec_ref(v_ctor_1795_);
lean_dec(v_name_1794_);
lean_dec(v_numParams_1793_);
lean_dec(v_ctorSyntax_1792_);
lean_dec_ref(v_infos_1791_);
return v___x_1842_;
}
}
v___jp_1806_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_toConstantVal_1815_; lean_object* v_toConstantVal_1816_; lean_object* v_levelParams_1817_; lean_object* v_name_1818_; lean_object* v_levelParams_1819_; lean_object* v_type_1820_; lean_object* v___x_1821_; size_t v_sz_1822_; size_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_borrowed(v___x_1803_, v_infos_1791_, v___x_1813_);
v_toConstantVal_1815_ = lean_ctor_get(v___x_1814_, 0);
v_toConstantVal_1816_ = lean_ctor_get(v_ctor_1795_, 0);
lean_inc_ref(v_toConstantVal_1816_);
lean_dec_ref(v_ctor_1795_);
v_levelParams_1817_ = lean_ctor_get(v_toConstantVal_1815_, 1);
lean_inc(v_levelParams_1817_);
v_name_1818_ = lean_ctor_get(v_toConstantVal_1816_, 0);
lean_inc(v_name_1818_);
v_levelParams_1819_ = lean_ctor_get(v_toConstantVal_1816_, 1);
lean_inc(v_levelParams_1819_);
v_type_1820_ = lean_ctor_get(v_toConstantVal_1816_, 2);
lean_inc_ref(v_type_1820_);
lean_dec_ref(v_toConstantVal_1816_);
v___x_1821_ = lean_array_get_size(v_infos_1791_);
v_sz_1822_ = lean_array_size(v_infos_1791_);
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1822_, v___x_1823_, v_infos_1791_);
v___x_1825_ = lean_box(0);
v___x_1826_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1817_, v___x_1825_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1793_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed), 21, 12);
lean_closure_set(v___f_1828_, 0, v___x_1813_);
lean_closure_set(v___f_1828_, 1, v_numParams_1793_);
lean_closure_set(v___f_1828_, 2, v___x_1824_);
lean_closure_set(v___f_1828_, 3, v___x_1826_);
lean_closure_set(v___f_1828_, 4, v___x_1827_);
lean_closure_set(v___f_1828_, 5, v___x_1821_);
lean_closure_set(v___f_1828_, 6, v_name_1794_);
lean_closure_set(v___f_1828_, 7, v_name_1818_);
lean_closure_set(v___f_1828_, 8, v_cls_1804_);
lean_closure_set(v___f_1828_, 9, v_levelParams_1819_);
lean_closure_set(v___f_1828_, 10, v_ctorSyntax_1792_);
lean_closure_set(v___f_1828_, 11, v___f_1805_);
v___x_1829_ = lean_nat_add(v_numParams_1793_, v___x_1821_);
lean_dec(v_numParams_1793_);
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
v___x_1831_ = 0;
v___x_1832_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1820_, v___x_1830_, v___f_1828_, v___x_1831_, v___x_1831_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1843_, lean_object* v_ctorSyntax_1844_, lean_object* v_numParams_1845_, lean_object* v_name_1846_, lean_object* v_ctor_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1843_, v_ctorSyntax_1844_, v_numParams_1845_, v_name_1846_, v_ctor_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_mvarId_1856_, lean_object* v_val_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; 
v___x_1865_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1856_, v_val_1857_, v___y_1861_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_mvarId_1866_, lean_object* v_val_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1866_, v_val_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_cls_1876_, lean_object* v_msg_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1876_, v_msg_1877_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_cls_1886_, lean_object* v_msg_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1886_, v_msg_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1895_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_instMonadEIO___redArg();
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v_toApplicative_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_2004_; 
v___x_1911_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1912_ = l_StateRefT_x27_instMonad___redArg(v___x_1911_);
v_toApplicative_1913_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1912_, 1);
lean_dec(v_unused_2005_);
v___x_1915_ = v___x_1912_;
v_isShared_1916_ = v_isSharedCheck_2004_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_toApplicative_1913_);
lean_dec(v___x_1912_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_2004_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v_toFunctor_1917_; lean_object* v_toSeq_1918_; lean_object* v_toSeqLeft_1919_; lean_object* v_toSeqRight_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_2002_; 
v_toFunctor_1917_ = lean_ctor_get(v_toApplicative_1913_, 0);
v_toSeq_1918_ = lean_ctor_get(v_toApplicative_1913_, 2);
v_toSeqLeft_1919_ = lean_ctor_get(v_toApplicative_1913_, 3);
v_toSeqRight_1920_ = lean_ctor_get(v_toApplicative_1913_, 4);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_toApplicative_1913_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; 
v_unused_2003_ = lean_ctor_get(v_toApplicative_1913_, 1);
lean_dec(v_unused_2003_);
v___x_1922_ = v_toApplicative_1913_;
v_isShared_1923_ = v_isSharedCheck_2002_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_toSeqRight_1920_);
lean_inc(v_toSeqLeft_1919_);
lean_inc(v_toSeq_1918_);
lean_inc(v_toFunctor_1917_);
lean_dec(v_toApplicative_1913_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_2002_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___f_1926_; lean_object* v___f_1927_; lean_object* v___x_1928_; lean_object* v___f_1929_; lean_object* v___f_1930_; lean_object* v___f_1931_; lean_object* v___x_1933_; 
v___f_1924_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1925_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1917_);
v___f_1926_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1926_, 0, v_toFunctor_1917_);
v___f_1927_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1927_, 0, v_toFunctor_1917_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___f_1926_);
lean_ctor_set(v___x_1928_, 1, v___f_1927_);
v___f_1929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1929_, 0, v_toSeqRight_1920_);
v___f_1930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1930_, 0, v_toSeqLeft_1919_);
v___f_1931_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1931_, 0, v_toSeq_1918_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 4, v___f_1929_);
lean_ctor_set(v___x_1922_, 3, v___f_1930_);
lean_ctor_set(v___x_1922_, 2, v___f_1931_);
lean_ctor_set(v___x_1922_, 1, v___f_1924_);
lean_ctor_set(v___x_1922_, 0, v___x_1928_);
v___x_1933_ = v___x_1922_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___f_1924_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v___f_1931_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v___f_1930_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v___f_1929_);
v___x_1933_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___f_1925_);
lean_ctor_set(v___x_1915_, 0, v___x_1933_);
v___x_1935_ = v___x_1915_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___f_1925_);
v___x_1935_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v_toApplicative_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1998_; 
v___x_1936_ = l_StateRefT_x27_instMonad___redArg(v___x_1935_);
v_toApplicative_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v___x_1936_, 1);
lean_dec(v_unused_1999_);
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1998_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_toApplicative_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1998_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v_toFunctor_1941_; lean_object* v_toSeq_1942_; lean_object* v_toSeqLeft_1943_; lean_object* v_toSeqRight_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1996_; 
v_toFunctor_1941_ = lean_ctor_get(v_toApplicative_1937_, 0);
v_toSeq_1942_ = lean_ctor_get(v_toApplicative_1937_, 2);
v_toSeqLeft_1943_ = lean_ctor_get(v_toApplicative_1937_, 3);
v_toSeqRight_1944_ = lean_ctor_get(v_toApplicative_1937_, 4);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_toApplicative_1937_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v_toApplicative_1937_, 1);
lean_dec(v_unused_1997_);
v___x_1946_ = v_toApplicative_1937_;
v_isShared_1947_ = v_isSharedCheck_1996_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_toSeqRight_1944_);
lean_inc(v_toSeqLeft_1943_);
lean_inc(v_toSeq_1942_);
lean_inc(v_toFunctor_1941_);
lean_dec(v_toApplicative_1937_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1996_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___f_1955_; lean_object* v___x_1957_; 
v___f_1948_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1949_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1941_);
v___f_1950_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1950_, 0, v_toFunctor_1941_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toFunctor_1941_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___f_1950_);
lean_ctor_set(v___x_1952_, 1, v___f_1951_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeqRight_1944_);
v___f_1954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1954_, 0, v_toSeqLeft_1943_);
v___f_1955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1955_, 0, v_toSeq_1942_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 4, v___f_1953_);
lean_ctor_set(v___x_1946_, 3, v___f_1954_);
lean_ctor_set(v___x_1946_, 2, v___f_1955_);
lean_ctor_set(v___x_1946_, 1, v___f_1948_);
lean_ctor_set(v___x_1946_, 0, v___x_1952_);
v___x_1957_ = v___x_1946_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___f_1948_);
lean_ctor_set(v_reuseFailAlloc_1995_, 2, v___f_1955_);
lean_ctor_set(v_reuseFailAlloc_1995_, 3, v___f_1954_);
lean_ctor_set(v_reuseFailAlloc_1995_, 4, v___f_1953_);
v___x_1957_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v___f_1949_);
lean_ctor_set(v___x_1939_, 0, v___x_1957_);
v___x_1959_ = v___x_1939_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___f_1949_);
v___x_1959_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1960_; lean_object* v_toApplicative_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1992_; 
v___x_1960_ = l_StateRefT_x27_instMonad___redArg(v___x_1959_);
v_toApplicative_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v___x_1960_, 1);
lean_dec(v_unused_1993_);
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1992_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_toApplicative_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1992_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v_toFunctor_1965_; lean_object* v_toSeq_1966_; lean_object* v_toSeqLeft_1967_; lean_object* v_toSeqRight_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1990_; 
v_toFunctor_1965_ = lean_ctor_get(v_toApplicative_1961_, 0);
v_toSeq_1966_ = lean_ctor_get(v_toApplicative_1961_, 2);
v_toSeqLeft_1967_ = lean_ctor_get(v_toApplicative_1961_, 3);
v_toSeqRight_1968_ = lean_ctor_get(v_toApplicative_1961_, 4);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_toApplicative_1961_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v_toApplicative_1961_, 1);
lean_dec(v_unused_1991_);
v___x_1970_ = v_toApplicative_1961_;
v_isShared_1971_ = v_isSharedCheck_1990_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_toSeqRight_1968_);
lean_inc(v_toSeqLeft_1967_);
lean_inc(v_toSeq_1966_);
lean_inc(v_toFunctor_1965_);
lean_dec(v_toApplicative_1961_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1990_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___x_1976_; lean_object* v___f_1977_; lean_object* v___f_1978_; lean_object* v___f_1979_; lean_object* v___x_1981_; 
v___f_1972_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_1973_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1965_);
v___f_1974_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1974_, 0, v_toFunctor_1965_);
v___f_1975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1975_, 0, v_toFunctor_1965_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___f_1974_);
lean_ctor_set(v___x_1976_, 1, v___f_1975_);
v___f_1977_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1977_, 0, v_toSeqRight_1968_);
v___f_1978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1978_, 0, v_toSeqLeft_1967_);
v___f_1979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1979_, 0, v_toSeq_1966_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 4, v___f_1977_);
lean_ctor_set(v___x_1970_, 3, v___f_1978_);
lean_ctor_set(v___x_1970_, 2, v___f_1979_);
lean_ctor_set(v___x_1970_, 1, v___f_1972_);
lean_ctor_set(v___x_1970_, 0, v___x_1976_);
v___x_1981_ = v___x_1970_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___f_1972_);
lean_ctor_set(v_reuseFailAlloc_1989_, 2, v___f_1979_);
lean_ctor_set(v_reuseFailAlloc_1989_, 3, v___f_1978_);
lean_ctor_set(v_reuseFailAlloc_1989_, 4, v___f_1977_);
v___x_1981_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1983_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 1, v___f_1973_);
lean_ctor_set(v___x_1963_, 0, v___x_1981_);
v___x_1983_ = v___x_1963_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1981_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v___f_1973_);
v___x_1983_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_3785__overap_1986_; lean_object* v___x_1987_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = l_instInhabitedOfMonad___redArg(v___x_1983_, v___x_1984_);
v___x_3785__overap_1986_ = lean_panic_fn_borrowed(v___x_1985_, v_msg_1903_);
lean_dec(v___x_1985_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
v___x_1987_ = lean_apply_7(v___x_3785__overap_1986_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, lean_box(0));
return v___x_1987_;
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
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
return v_res_2014_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2015_, lean_object* v_opt_2016_){
_start:
{
lean_object* v_name_2017_; lean_object* v_defValue_2018_; lean_object* v_map_2019_; lean_object* v___x_2020_; 
v_name_2017_ = lean_ctor_get(v_opt_2016_, 0);
v_defValue_2018_ = lean_ctor_get(v_opt_2016_, 1);
v_map_2019_ = lean_ctor_get(v_opts_2015_, 0);
v___x_2020_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2019_, v_name_2017_);
if (lean_obj_tag(v___x_2020_) == 0)
{
uint8_t v___x_2021_; 
v___x_2021_ = lean_unbox(v_defValue_2018_);
return v___x_2021_;
}
else
{
lean_object* v_val_2022_; 
v_val_2022_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_val_2022_);
lean_dec_ref_known(v___x_2020_, 1);
if (lean_obj_tag(v_val_2022_) == 1)
{
uint8_t v_v_2023_; 
v_v_2023_ = lean_ctor_get_uint8(v_val_2022_, 0);
lean_dec_ref_known(v_val_2022_, 0);
return v_v_2023_;
}
else
{
uint8_t v___x_2024_; 
lean_dec(v_val_2022_);
v___x_2024_ = lean_unbox(v_defValue_2018_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2025_, lean_object* v_opt_2026_){
_start:
{
uint8_t v_res_2027_; lean_object* v_r_2028_; 
v_res_2027_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2025_, v_opt_2026_);
lean_dec_ref(v_opt_2026_);
lean_dec_ref(v_opts_2025_);
v_r_2028_ = lean_box(v_res_2027_);
return v_r_2028_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2029_ = lean_box(1);
v___x_2030_ = l_Lean_MessageData_ofFormat(v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2035_ = l_Lean_MessageData_ofFormat(v___x_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 0)
{
return v_x_2036_;
}
else
{
lean_object* v_head_2038_; lean_object* v_tail_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2061_; 
v_head_2038_ = lean_ctor_get(v_x_2037_, 0);
v_tail_2039_ = lean_ctor_get(v_x_2037_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_x_2037_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2041_ = v_x_2037_;
v_isShared_2042_ = v_isSharedCheck_2061_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_tail_2039_);
lean_inc(v_head_2038_);
lean_dec(v_x_2037_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2061_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_before_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2059_; 
v_before_2043_ = lean_ctor_get(v_head_2038_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_head_2038_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v_head_2038_, 1);
lean_dec(v_unused_2060_);
v___x_2045_ = v_head_2038_;
v_isShared_2046_ = v_isSharedCheck_2059_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_before_2043_);
lean_dec(v_head_2038_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2059_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2046_ == 0)
{
lean_ctor_set_tag(v___x_2045_, 7);
lean_ctor_set(v___x_2045_, 1, v___x_2047_);
lean_ctor_set(v___x_2045_, 0, v_x_2036_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_x_2036_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2050_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 7);
lean_ctor_set(v___x_2041_, 1, v___x_2050_);
lean_ctor_set(v___x_2041_, 0, v___x_2049_);
v___x_2052_ = v___x_2041_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2049_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = l_Lean_MessageData_ofSyntax(v_before_2043_);
v___x_2054_ = l_Lean_indentD(v___x_2053_);
v___x_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2052_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
v_x_2036_ = v___x_2055_;
v_x_2037_ = v_tail_2039_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2066_ = l_Lean_MessageData_ofFormat(v___x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2067_, lean_object* v_macroStack_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2071_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2069_);
v___x_2072_ = l_Lean_Elab_pp_macroStack;
v___x_2073_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v___x_2071_, v___x_2072_);
lean_dec_ref(v___x_2071_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_dec(v_macroStack_2068_);
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_msgData_2067_);
return v___x_2074_;
}
else
{
if (lean_obj_tag(v_macroStack_2068_) == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_msgData_2067_);
return v___x_2075_;
}
else
{
lean_object* v_head_2076_; lean_object* v_after_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2092_; 
v_head_2076_ = lean_ctor_get(v_macroStack_2068_, 0);
lean_inc(v_head_2076_);
v_after_2077_ = lean_ctor_get(v_head_2076_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_head_2076_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v_head_2076_, 0);
lean_dec(v_unused_2093_);
v___x_2079_ = v_head_2076_;
v_isShared_2080_ = v_isSharedCheck_2092_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_after_2077_);
lean_dec(v_head_2076_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2092_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2080_ == 0)
{
lean_ctor_set_tag(v___x_2079_, 7);
lean_ctor_set(v___x_2079_, 1, v___x_2081_);
lean_ctor_set(v___x_2079_, 0, v_msgData_2067_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_msgData_2067_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_msgData_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2084_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2085_, 0, v___x_2083_);
lean_ctor_set(v___x_2085_, 1, v___x_2084_);
v___x_2086_ = l_Lean_MessageData_ofSyntax(v_after_2077_);
v___x_2087_ = l_Lean_indentD(v___x_2086_);
v_msgData_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2088_, 0, v___x_2085_);
lean_ctor_set(v_msgData_2088_, 1, v___x_2087_);
v___x_2089_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2088_, v_macroStack_2068_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2094_, lean_object* v_macroStack_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2094_, v_macroStack_2095_, v___y_2096_);
lean_dec_ref(v___y_2096_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_ref_2107_; lean_object* v_macroStack_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v_a_2111_; lean_object* v___x_2112_; lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2121_; 
v_ref_2107_ = lean_ctor_get(v___y_2104_, 2);
v_macroStack_2108_ = lean_ctor_get(v___y_2100_, 1);
v___x_2109_ = l_Lean_Elab_getBetterRef(v_ref_2107_, v_macroStack_2108_);
v___x_2110_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2099_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref(v___x_2110_);
lean_inc(v_macroStack_2108_);
v___x_2112_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2111_, v_macroStack_2108_, v___y_2104_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2121_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2121_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2109_);
lean_ctor_set(v___x_2117_, 1, v_a_2113_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set_tag(v___x_2115_, 1);
lean_ctor_set(v___x_2115_, 0, v___x_2117_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2130_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2140_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2141_ = lean_unsigned_to_nat(11u);
v___x_2142_ = lean_unsigned_to_nat(122u);
v___x_2143_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2144_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2145_ = l_mkPanicMessageWithDecl(v___x_2144_, v___x_2143_, v___x_2142_, v___x_2141_, v___x_2140_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2162_; lean_object* v_env_2163_; uint8_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2162_ = lean_st_ref_get(v___y_2152_);
v_env_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref(v_env_2163_);
lean_dec(v___x_2162_);
v___x_2164_ = 0;
lean_inc(v_constName_2146_);
v___x_2165_ = l_Lean_Environment_findAsync_x3f(v_env_2163_, v_constName_2146_, v___x_2164_);
if (lean_obj_tag(v___x_2165_) == 1)
{
lean_object* v_val_2166_; uint8_t v_kind_2167_; 
v_val_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v___x_2165_, 1);
v_kind_2167_ = lean_ctor_get_uint8(v_val_2166_, sizeof(void*)*3);
if (v_kind_2167_ == 6)
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2166_);
if (lean_obj_tag(v___x_2168_) == 6)
{
lean_object* v_val_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_constName_2146_);
v_val_2169_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2168_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_val_2169_);
lean_dec(v___x_2168_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
lean_ctor_set_tag(v___x_2171_, 0);
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_val_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v___x_2168_);
v___x_2177_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2178_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2177_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2187_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2187_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
if (lean_obj_tag(v_a_2179_) == 0)
{
lean_del_object(v___x_2181_);
goto v___jp_2154_;
}
else
{
lean_object* v_val_2183_; lean_object* v___x_2185_; 
lean_dec(v_constName_2146_);
v_val_2183_ = lean_ctor_get(v_a_2179_, 0);
lean_inc(v_val_2183_);
lean_dec_ref_known(v_a_2179_, 1);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 0, v_val_2183_);
v___x_2185_ = v___x_2181_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_val_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_dec(v_constName_2146_);
v_a_2188_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2178_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2178_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2193_; 
if (v_isShared_2191_ == 0)
{
v___x_2193_ = v___x_2190_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_a_2188_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
}
}
else
{
lean_dec(v_val_2166_);
goto v___jp_2154_;
}
}
else
{
lean_dec(v___x_2165_);
goto v___jp_2154_;
}
v___jp_2154_:
{
lean_object* v___x_2155_; uint8_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2155_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2156_ = 0;
v___x_2157_ = l_Lean_MessageData_ofConstName(v_constName_2146_, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2155_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2160_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2205_, lean_object* v_infos_2206_, lean_object* v_numParams_2207_, lean_object* v_as_x27_2208_, lean_object* v_b_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
if (lean_obj_tag(v_as_x27_2208_) == 0)
{
lean_object* v___x_2217_; 
lean_dec(v_numParams_2207_);
lean_dec_ref(v_infos_2206_);
lean_dec_ref(v_a_2205_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v_b_2209_);
return v___x_2217_;
}
else
{
lean_object* v_head_2218_; lean_object* v_tail_2219_; lean_object* v_array_2220_; lean_object* v_start_2221_; lean_object* v_stop_2222_; uint8_t v___x_2223_; 
v_head_2218_ = lean_ctor_get(v_as_x27_2208_, 0);
v_tail_2219_ = lean_ctor_get(v_as_x27_2208_, 1);
v_array_2220_ = lean_ctor_get(v_b_2209_, 0);
v_start_2221_ = lean_ctor_get(v_b_2209_, 1);
v_stop_2222_ = lean_ctor_get(v_b_2209_, 2);
v___x_2223_ = lean_nat_dec_lt(v_start_2221_, v_stop_2222_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; 
lean_dec(v_numParams_2207_);
lean_dec_ref(v_infos_2206_);
lean_dec_ref(v_a_2205_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v_b_2209_);
return v___x_2224_;
}
else
{
lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2256_; 
lean_inc(v_stop_2222_);
lean_inc(v_start_2221_);
lean_inc_ref(v_array_2220_);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_b_2209_);
if (v_isSharedCheck_2256_ == 0)
{
lean_object* v_unused_2257_; lean_object* v_unused_2258_; lean_object* v_unused_2259_; 
v_unused_2257_ = lean_ctor_get(v_b_2209_, 2);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_b_2209_, 1);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_b_2209_, 0);
lean_dec(v_unused_2259_);
v___x_2226_ = v_b_2209_;
v_isShared_2227_ = v_isSharedCheck_2256_;
goto v_resetjp_2225_;
}
else
{
lean_dec(v_b_2209_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2256_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2228_ = lean_array_fget(v_array_2220_, v_start_2221_);
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_add(v_start_2221_, v___x_2229_);
lean_dec(v_start_2221_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2230_);
v___x_2232_ = v___x_2226_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_array_2220_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_stop_2222_);
v___x_2232_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; 
lean_inc(v_head_2218_);
v___x_2233_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2218_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_toConstantVal_2234_; lean_object* v_a_2235_; lean_object* v_name_2236_; lean_object* v___x_2237_; 
v_toConstantVal_2234_ = lean_ctor_get(v_a_2205_, 0);
v_a_2235_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2233_, 1);
v_name_2236_ = lean_ctor_get(v_toConstantVal_2234_, 0);
lean_inc(v_name_2236_);
lean_inc(v_numParams_2207_);
lean_inc_ref(v_infos_2206_);
v___x_2237_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2206_, v___x_2228_, v_numParams_2207_, v_name_2236_, v_a_2235_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_dec_ref_known(v___x_2237_, 1);
v_as_x27_2208_ = v_tail_2219_;
v_b_2209_ = v___x_2232_;
goto _start;
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v___x_2232_);
lean_dec(v_numParams_2207_);
lean_dec_ref(v_infos_2206_);
lean_dec_ref(v_a_2205_);
v_a_2239_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2237_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2237_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v___x_2232_);
lean_dec(v___x_2228_);
lean_dec(v_numParams_2207_);
lean_dec_ref(v_infos_2206_);
lean_dec_ref(v_a_2205_);
v_a_2247_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2233_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2233_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2260_, lean_object* v_infos_2261_, lean_object* v_numParams_2262_, lean_object* v_as_x27_2263_, lean_object* v_b_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2260_, v_infos_2261_, v_numParams_2262_, v_as_x27_2263_, v_b_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_as_x27_2263_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2273_, lean_object* v_numParams_2274_, lean_object* v_as_2275_, size_t v_sz_2276_, size_t v_i_2277_, lean_object* v_b_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
uint8_t v___x_2286_; 
v___x_2286_ = lean_usize_dec_lt(v_i_2277_, v_sz_2276_);
if (v___x_2286_ == 0)
{
lean_object* v___x_2287_; 
lean_dec(v_numParams_2274_);
lean_dec_ref(v_infos_2273_);
v___x_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2287_, 0, v_b_2278_);
return v___x_2287_;
}
else
{
lean_object* v_array_2288_; lean_object* v_start_2289_; lean_object* v_stop_2290_; uint8_t v___x_2291_; 
v_array_2288_ = lean_ctor_get(v_b_2278_, 0);
v_start_2289_ = lean_ctor_get(v_b_2278_, 1);
v_stop_2290_ = lean_ctor_get(v_b_2278_, 2);
v___x_2291_ = lean_nat_dec_lt(v_start_2289_, v_stop_2290_);
if (v___x_2291_ == 0)
{
lean_object* v___x_2292_; 
lean_dec(v_numParams_2274_);
lean_dec_ref(v_infos_2273_);
v___x_2292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2292_, 0, v_b_2278_);
return v___x_2292_;
}
else
{
lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2320_; 
lean_inc(v_stop_2290_);
lean_inc(v_start_2289_);
lean_inc_ref(v_array_2288_);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_b_2278_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; lean_object* v_unused_2322_; lean_object* v_unused_2323_; 
v_unused_2321_ = lean_ctor_get(v_b_2278_, 2);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_b_2278_, 1);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_b_2278_, 0);
lean_dec(v_unused_2323_);
v___x_2294_ = v_b_2278_;
v_isShared_2295_ = v_isSharedCheck_2320_;
goto v_resetjp_2293_;
}
else
{
lean_dec(v_b_2278_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2320_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v_ctorSyntax_2297_; lean_object* v_a_2298_; lean_object* v_ctors_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2296_ = lean_array_fget_borrowed(v_array_2288_, v_start_2289_);
v_ctorSyntax_2297_ = lean_ctor_get(v___x_2296_, 4);
lean_inc_ref(v_ctorSyntax_2297_);
v_a_2298_ = lean_array_uget_borrowed(v_as_2275_, v_i_2277_);
v_ctors_2299_ = lean_ctor_get(v_a_2298_, 4);
v___x_2300_ = lean_array_get_size(v_ctorSyntax_2297_);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v_start_2289_, v___x_2301_);
lean_dec(v_start_2289_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2302_);
v___x_2304_ = v___x_2294_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_array_2288_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_stop_2290_);
v___x_2304_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_unsigned_to_nat(0u);
v___x_2306_ = l_Array_toSubarray___redArg(v_ctorSyntax_2297_, v___x_2305_, v___x_2300_);
lean_inc(v_numParams_2274_);
lean_inc_ref(v_infos_2273_);
lean_inc(v_a_2298_);
v___x_2307_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2298_, v_infos_2273_, v_numParams_2274_, v_ctors_2299_, v___x_2306_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2307_) == 0)
{
size_t v___x_2308_; size_t v___x_2309_; 
lean_dec_ref_known(v___x_2307_, 1);
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_add(v_i_2277_, v___x_2308_);
v_i_2277_ = v___x_2309_;
v_b_2278_ = v___x_2304_;
goto _start;
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_dec_ref(v___x_2304_);
lean_dec(v_numParams_2274_);
lean_dec_ref(v_infos_2273_);
v_a_2311_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2307_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2307_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2324_, lean_object* v_numParams_2325_, lean_object* v_as_2326_, lean_object* v_sz_2327_, lean_object* v_i_2328_, lean_object* v_b_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
size_t v_sz_boxed_2337_; size_t v_i_boxed_2338_; lean_object* v_res_2339_; 
v_sz_boxed_2337_ = lean_unbox_usize(v_sz_2327_);
lean_dec(v_sz_2327_);
v_i_boxed_2338_ = lean_unbox_usize(v_i_2328_);
lean_dec(v_i_2328_);
v_res_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2324_, v_numParams_2325_, v_as_2326_, v_sz_boxed_2337_, v_i_boxed_2338_, v_b_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec_ref(v_as_2326_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2340_, lean_object* v_infos_2341_, lean_object* v_coinductiveElabData_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; size_t v_sz_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = lean_array_get_size(v_coinductiveElabData_2342_);
v___x_2352_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2342_, v___x_2350_, v___x_2351_);
v_sz_2353_ = lean_array_size(v_infos_2341_);
v___x_2354_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2341_);
v___x_2355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2341_, v_numParams_2340_, v_infos_2341_, v_sz_2353_, v___x_2354_, v___x_2352_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_);
lean_dec_ref(v_infos_2341_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2363_; 
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; 
v_unused_2364_ = lean_ctor_get(v___x_2355_, 0);
lean_dec(v_unused_2364_);
v___x_2357_ = v___x_2355_;
v_isShared_2358_ = v_isSharedCheck_2363_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v___x_2355_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2363_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2361_; 
v___x_2359_ = lean_box(0);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2359_);
v___x_2361_ = v___x_2357_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
v_a_2365_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2355_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2355_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2373_, lean_object* v_infos_2374_, lean_object* v_coinductiveElabData_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2373_, v_infos_2374_, v_coinductiveElabData_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2384_, lean_object* v_infos_2385_, lean_object* v_numParams_2386_, lean_object* v_as_2387_, lean_object* v_as_x27_2388_, lean_object* v_b_2389_, lean_object* v_a_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2384_, v_infos_2385_, v_numParams_2386_, v_as_x27_2388_, v_b_2389_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2399_, lean_object* v_infos_2400_, lean_object* v_numParams_2401_, lean_object* v_as_2402_, lean_object* v_as_x27_2403_, lean_object* v_b_2404_, lean_object* v_a_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2399_, v_infos_2400_, v_numParams_2401_, v_as_2402_, v_as_x27_2403_, v_b_2404_, v_a_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v_as_x27_2403_);
lean_dec(v_as_2402_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2414_, lean_object* v_msg_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2424_, lean_object* v_msg_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2424_, v_msg_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2434_, lean_object* v_macroStack_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; 
v___x_2443_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2434_, v_macroStack_2435_, v___y_2440_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2444_, lean_object* v_macroStack_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2444_, v_macroStack_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_mvarId_2454_, lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2454_, v_x_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
v_a_2470_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2461_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2461_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_mvarId_2478_, lean_object* v_x_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2478_, v_x_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2486_, lean_object* v_mvarId_2487_, lean_object* v_x_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2487_, v_x_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2495_, lean_object* v_mvarId_2496_, lean_object* v_x_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2495_, v_mvarId_2496_, v_x_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_type_2504_, lean_object* v_maxFVars_x3f_2505_, lean_object* v_k_2506_, uint8_t v_cleanupAnnotations_2507_, uint8_t v_whnfType_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___f_2514_; lean_object* v___x_2515_; 
v___f_2514_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2514_, 0, v_k_2506_);
v___x_2515_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2504_, v_maxFVars_x3f_2505_, v___f_2514_, v_cleanupAnnotations_2507_, v_whnfType_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
v_a_2524_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2515_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2515_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_type_2532_, lean_object* v_maxFVars_x3f_2533_, lean_object* v_k_2534_, lean_object* v_cleanupAnnotations_2535_, lean_object* v_whnfType_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2542_; uint8_t v_whnfType_boxed_2543_; lean_object* v_res_2544_; 
v_cleanupAnnotations_boxed_2542_ = lean_unbox(v_cleanupAnnotations_2535_);
v_whnfType_boxed_2543_ = lean_unbox(v_whnfType_2536_);
v_res_2544_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2532_, v_maxFVars_x3f_2533_, v_k_2534_, v_cleanupAnnotations_boxed_2542_, v_whnfType_boxed_2543_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2545_, lean_object* v_type_2546_, lean_object* v_maxFVars_x3f_2547_, lean_object* v_k_2548_, uint8_t v_cleanupAnnotations_2549_, uint8_t v_whnfType_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2546_, v_maxFVars_x3f_2547_, v_k_2548_, v_cleanupAnnotations_2549_, v_whnfType_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2557_, lean_object* v_type_2558_, lean_object* v_maxFVars_x3f_2559_, lean_object* v_k_2560_, lean_object* v_cleanupAnnotations_2561_, lean_object* v_whnfType_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2568_; uint8_t v_whnfType_boxed_2569_; lean_object* v_res_2570_; 
v_cleanupAnnotations_boxed_2568_ = lean_unbox(v_cleanupAnnotations_2561_);
v_whnfType_boxed_2569_ = lean_unbox(v_whnfType_2562_);
v_res_2570_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2557_, v_type_2558_, v_maxFVars_x3f_2559_, v_k_2560_, v_cleanupAnnotations_boxed_2568_, v_whnfType_boxed_2569_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2571_, lean_object* v_msg_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v_toCold_2578_; lean_object* v_currRecDepth_2579_; lean_object* v_ref_2580_; uint16_t v_optionFlags_2581_; uint8_t v_suppressElabErrors_2582_; uint8_t v_isRecordingDeps_2583_; lean_object* v_ref_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_toCold_2578_ = lean_ctor_get(v___y_2575_, 0);
v_currRecDepth_2579_ = lean_ctor_get(v___y_2575_, 1);
v_ref_2580_ = lean_ctor_get(v___y_2575_, 2);
v_optionFlags_2581_ = lean_ctor_get_uint16(v___y_2575_, sizeof(void*)*3);
v_suppressElabErrors_2582_ = lean_ctor_get_uint8(v___y_2575_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2583_ = lean_ctor_get_uint8(v___y_2575_, sizeof(void*)*3 + 3);
v_ref_2584_ = l_Lean_replaceRef(v_ref_2571_, v_ref_2580_);
lean_inc(v_currRecDepth_2579_);
lean_inc_ref(v_toCold_2578_);
v___x_2585_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2585_, 0, v_toCold_2578_);
lean_ctor_set(v___x_2585_, 1, v_currRecDepth_2579_);
lean_ctor_set(v___x_2585_, 2, v_ref_2584_);
lean_ctor_set_uint16(v___x_2585_, sizeof(void*)*3, v_optionFlags_2581_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3 + 2, v_suppressElabErrors_2582_);
lean_ctor_set_uint8(v___x_2585_, sizeof(void*)*3 + 3, v_isRecordingDeps_2583_);
v___x_2586_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2572_, v___y_2573_, v___y_2574_, v___x_2585_, v___y_2576_);
lean_dec_ref_known(v___x_2585_, 3);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2587_, lean_object* v_msg_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2587_, v_msg_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v_ref_2587_);
return v_res_2594_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2598_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2599_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2600_ = lean_unsigned_to_nat(0u);
v___x_2601_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___x_2600_);
lean_ctor_set(v___x_2601_, 2, v___x_2600_);
lean_ctor_set(v___x_2601_, 3, v___x_2600_);
lean_ctor_set(v___x_2601_, 4, v___x_2599_);
lean_ctor_set(v___x_2601_, 5, v___x_2599_);
lean_ctor_set(v___x_2601_, 6, v___x_2599_);
lean_ctor_set(v___x_2601_, 7, v___x_2599_);
lean_ctor_set(v___x_2601_, 8, v___x_2599_);
lean_ctor_set(v___x_2601_, 9, v___x_2599_);
lean_ctor_set(v___x_2601_, 10, v___x_2599_);
lean_ctor_set(v___x_2601_, 11, v___x_2598_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_unsigned_to_nat(32u);
v___x_2603_ = lean_mk_empty_array_with_capacity(v___x_2602_);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2605_ = ((size_t)5ULL);
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_unsigned_to_nat(32u);
v___x_2608_ = lean_mk_empty_array_with_capacity(v___x_2607_);
v___x_2609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2610_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2608_);
lean_ctor_set(v___x_2610_, 2, v___x_2606_);
lean_ctor_set(v___x_2610_, 3, v___x_2606_);
lean_ctor_set_usize(v___x_2610_, 4, v___x_2605_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2611_ = lean_box(1);
v___x_2612_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
lean_ctor_set(v___x_2614_, 1, v___x_2612_);
lean_ctor_set(v___x_2614_, 2, v___x_2611_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2617_ = l_Lean_stringToMessageData(v___x_2616_);
return v___x_2617_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2620_ = l_Lean_stringToMessageData(v___x_2619_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2623_ = l_Lean_stringToMessageData(v___x_2622_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2626_ = l_Lean_stringToMessageData(v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2629_ = l_Lean_stringToMessageData(v___x_2628_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2635_ = l_Lean_stringToMessageData(v___x_2634_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2636_, lean_object* v_declHint_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_env_2642_; uint8_t v___x_2643_; 
v___x_2640_ = lean_box(0);
v___x_2641_ = lean_st_ref_get(v___y_2638_);
v_env_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc_ref(v_env_2642_);
lean_dec(v___x_2641_);
v___x_2643_ = l_Lean_Name_isAnonymous(v_declHint_2637_);
if (v___x_2643_ == 0)
{
uint8_t v_isExporting_2644_; 
v_isExporting_2644_ = lean_ctor_get_uint8(v_env_2642_, sizeof(void*)*13);
if (v_isExporting_2644_ == 0)
{
lean_object* v___x_2645_; 
lean_dec_ref(v_env_2642_);
lean_dec(v_declHint_2637_);
v___x_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2645_, 0, v_msg_2636_);
return v___x_2645_;
}
else
{
lean_object* v___x_2646_; uint8_t v___x_2647_; 
lean_inc_ref(v_env_2642_);
v___x_2646_ = l_Lean_Environment_setExporting(v_env_2642_, v___x_2643_);
lean_inc(v_declHint_2637_);
lean_inc_ref(v___x_2646_);
v___x_2647_ = l_Lean_Environment_contains(v___x_2646_, v_declHint_2637_, v_isExporting_2644_);
if (v___x_2647_ == 0)
{
lean_object* v___x_2648_; 
lean_dec_ref(v___x_2646_);
lean_dec_ref(v_env_2642_);
lean_dec(v_declHint_2637_);
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v_msg_2636_);
return v___x_2648_;
}
else
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v_c_2654_; lean_object* v___x_2655_; 
v___x_2649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2650_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2651_ = l_Lean_Options_empty;
v___x_2652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2646_);
lean_ctor_set(v___x_2652_, 1, v___x_2649_);
lean_ctor_set(v___x_2652_, 2, v___x_2650_);
lean_ctor_set(v___x_2652_, 3, v___x_2651_);
lean_inc(v_declHint_2637_);
v___x_2653_ = l_Lean_MessageData_ofConstName(v_declHint_2637_, v___x_2643_);
v_c_2654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2654_, 0, v___x_2652_);
lean_ctor_set(v_c_2654_, 1, v___x_2653_);
v___x_2655_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2642_, v_declHint_2637_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec_ref(v_env_2642_);
lean_dec(v_declHint_2637_);
v___x_2656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
lean_ctor_set(v___x_2657_, 1, v_c_2654_);
v___x_2658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = l_Lean_MessageData_note(v___x_2659_);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v_msg_2636_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
return v___x_2662_;
}
else
{
lean_object* v_val_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2697_; 
v_val_2663_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2665_ = v___x_2655_;
v_isShared_2666_ = v_isSharedCheck_2697_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_val_2663_);
lean_dec(v___x_2655_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2697_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v_moduleNames_2668_; lean_object* v_mod_2669_; uint8_t v___x_2670_; 
v___x_2667_ = l_Lean_Environment_header(v_env_2642_);
lean_dec_ref(v_env_2642_);
v_moduleNames_2668_ = lean_ctor_get(v___x_2667_, 4);
lean_inc_ref(v_moduleNames_2668_);
lean_dec_ref(v___x_2667_);
v_mod_2669_ = lean_array_get(v___x_2640_, v_moduleNames_2668_, v_val_2663_);
lean_dec(v_val_2663_);
lean_dec_ref(v_moduleNames_2668_);
v___x_2670_ = l_Lean_isPrivateName(v_declHint_2637_);
lean_dec(v_declHint_2637_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2682_; 
v___x_2671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v_c_2654_);
v___x_2673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = l_Lean_MessageData_ofName(v_mod_2669_);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_MessageData_note(v___x_2678_);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_msg_2636_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2680_);
v___x_2682_ = v___x_2665_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v_c_2654_);
v___x_2686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_MessageData_ofName(v_mod_2669_);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2689_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = l_Lean_MessageData_note(v___x_2691_);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_msg_2636_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set_tag(v___x_2665_, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2693_);
v___x_2695_ = v___x_2665_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2698_; 
lean_dec_ref(v_env_2642_);
lean_dec(v_declHint_2637_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_msg_2636_);
return v___x_2698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2699_, lean_object* v_declHint_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2699_, v_declHint_2700_, v___y_2701_);
lean_dec(v___y_2701_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2704_, lean_object* v_declHint_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v_a_2712_; lean_object* v___x_2714_; uint8_t v_isShared_2715_; uint8_t v_isSharedCheck_2721_; 
v___x_2711_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2704_, v_declHint_2705_, v___y_2709_);
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2714_ = v___x_2711_;
v_isShared_2715_ = v_isSharedCheck_2721_;
goto v_resetjp_2713_;
}
else
{
lean_inc(v_a_2712_);
lean_dec(v___x_2711_);
v___x_2714_ = lean_box(0);
v_isShared_2715_ = v_isSharedCheck_2721_;
goto v_resetjp_2713_;
}
v_resetjp_2713_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = l_Lean_unknownIdentifierMessageTag;
v___x_2717_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
lean_ctor_set(v___x_2717_, 1, v_a_2712_);
if (v_isShared_2715_ == 0)
{
lean_ctor_set(v___x_2714_, 0, v___x_2717_);
v___x_2719_ = v___x_2714_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2722_, lean_object* v_declHint_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2722_, v_declHint_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2730_, lean_object* v_msg_2731_, lean_object* v_declHint_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v_a_2739_; lean_object* v___x_2740_; 
v___x_2738_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2731_, v_declHint_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref(v___x_2738_);
v___x_2740_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2730_, v_a_2739_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2741_, lean_object* v_msg_2742_, lean_object* v_declHint_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2741_, v_msg_2742_, v_declHint_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v_ref_2741_);
return v_res_2749_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2753_, lean_object* v_constName_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2760_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2761_ = 0;
lean_inc(v_constName_2754_);
v___x_2762_ = l_Lean_MessageData_ofConstName(v_constName_2754_, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2760_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2763_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2753_, v___x_2765_, v_constName_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2767_, lean_object* v_constName_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2767_, v_constName_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v_ref_2767_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_ref_2781_; lean_object* v___x_2782_; 
v_ref_2781_ = lean_ctor_get(v___y_2778_, 2);
v___x_2782_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2781_, v_constName_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; lean_object* v_env_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; 
v___x_2796_ = lean_st_ref_get(v___y_2794_);
v_env_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc_ref(v_env_2797_);
lean_dec(v___x_2796_);
v___x_2798_ = 0;
lean_inc(v_constName_2790_);
v___x_2799_ = l_Lean_Environment_find_x3f(v_env_2797_, v_constName_2790_, v___x_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
return v___x_2800_;
}
else
{
lean_object* v_val_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_constName_2790_);
v_val_2801_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2799_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_val_2801_);
lean_dec(v___x_2799_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
lean_ctor_set_tag(v___x_2803_, 0);
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_val_2801_);
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
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
return v_res_2815_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2816_, lean_object* v_as_2817_, size_t v_i_2818_, size_t v_stop_2819_){
_start:
{
uint8_t v___x_2820_; 
v___x_2820_ = lean_usize_dec_eq(v_i_2818_, v_stop_2819_);
if (v___x_2820_ == 0)
{
lean_object* v___x_2821_; uint8_t v___x_2822_; 
v___x_2821_ = lean_array_uget_borrowed(v_as_2817_, v_i_2818_);
v___x_2822_ = l_Lean_Expr_isAppOf(v_e_2816_, v___x_2821_);
if (v___x_2822_ == 0)
{
size_t v___x_2823_; size_t v___x_2824_; 
v___x_2823_ = ((size_t)1ULL);
v___x_2824_ = lean_usize_add(v_i_2818_, v___x_2823_);
v_i_2818_ = v___x_2824_;
goto _start;
}
else
{
return v___x_2822_;
}
}
else
{
uint8_t v___x_2826_; 
v___x_2826_ = 0;
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2827_, lean_object* v_as_2828_, lean_object* v_i_2829_, lean_object* v_stop_2830_){
_start:
{
size_t v_i_boxed_2831_; size_t v_stop_boxed_2832_; uint8_t v_res_2833_; lean_object* v_r_2834_; 
v_i_boxed_2831_ = lean_unbox_usize(v_i_2829_);
lean_dec(v_i_2829_);
v_stop_boxed_2832_ = lean_unbox_usize(v_stop_2830_);
lean_dec(v_stop_2830_);
v_res_2833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2827_, v_as_2828_, v_i_boxed_2831_, v_stop_boxed_2832_);
lean_dec_ref(v_as_2828_);
lean_dec_ref(v_e_2827_);
v_r_2834_ = lean_box(v_res_2833_);
return v_r_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2835_, lean_object* v_name_2836_, lean_object* v___y_2837_, lean_object* v___x_2838_, lean_object* v_levels_2839_, lean_object* v_params_2840_, lean_object* v_e_2841_){
_start:
{
uint8_t v___x_2842_; 
v___x_2842_ = l_Lean_Expr_isApp(v_e_2841_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
lean_dec_ref(v_e_2841_);
lean_dec_ref(v_params_2840_);
lean_dec(v_levels_2839_);
lean_dec(v_name_2836_);
lean_dec(v_numParams_2835_);
v___x_2843_ = lean_box(0);
return v___x_2843_;
}
else
{
lean_object* v_dummy_2844_; lean_object* v_nargs_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v_dummy_2844_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2845_ = l_Lean_Expr_getAppNumArgs(v_e_2841_);
lean_inc(v_nargs_2845_);
v___x_2846_ = lean_mk_array(v_nargs_2845_, v_dummy_2844_);
v___x_2847_ = lean_unsigned_to_nat(1u);
v___x_2848_ = lean_nat_sub(v_nargs_2845_, v___x_2847_);
lean_dec(v_nargs_2845_);
lean_inc_ref(v_e_2841_);
v___x_2849_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2841_, v___x_2846_, v___x_2848_);
v___x_2850_ = lean_array_get_size(v___x_2849_);
v___x_2851_ = l_Array_toSubarray___redArg(v___x_2849_, v_numParams_2835_, v___x_2850_);
v___x_2852_ = l_Lean_Expr_isAppOf(v_e_2841_, v_name_2836_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; uint8_t v___x_2854_; 
lean_dec(v_name_2836_);
v___x_2853_ = lean_array_get_size(v___y_2837_);
v___x_2854_ = lean_nat_dec_lt(v___x_2838_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_e_2841_);
lean_dec_ref(v_params_2840_);
lean_dec(v_levels_2839_);
v___x_2855_ = lean_box(0);
return v___x_2855_;
}
else
{
if (v___x_2854_ == 0)
{
lean_object* v___x_2856_; 
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_e_2841_);
lean_dec_ref(v_params_2840_);
lean_dec(v_levels_2839_);
v___x_2856_ = lean_box(0);
return v___x_2856_;
}
else
{
size_t v___x_2857_; size_t v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = ((size_t)0ULL);
v___x_2858_ = lean_usize_of_nat(v___x_2853_);
v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2841_, v___y_2837_, v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_e_2841_);
lean_dec_ref(v_params_2840_);
lean_dec(v_levels_2839_);
v___x_2860_ = lean_box(0);
return v___x_2860_;
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2861_ = l_Lean_Expr_getAppFn(v_e_2841_);
lean_dec_ref(v_e_2841_);
v___x_2862_ = l_Lean_Expr_constName(v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2862_);
v___x_2864_ = l_Lean_mkConst(v___x_2863_, v_levels_2839_);
v___x_2865_ = l_Subarray_copy___redArg(v___x_2851_);
v___x_2866_ = l_Array_append___redArg(v_params_2840_, v___x_2865_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = l_Lean_mkAppN(v___x_2864_, v___x_2866_);
lean_dec_ref(v___x_2866_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
return v___x_2868_;
}
}
}
}
else
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
lean_dec_ref(v_e_2841_);
v___x_2869_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2836_);
v___x_2870_ = l_Lean_mkConst(v___x_2869_, v_levels_2839_);
v___x_2871_ = l_Subarray_copy___redArg(v___x_2851_);
v___x_2872_ = l_Array_append___redArg(v_params_2840_, v___x_2871_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = l_Lean_mkAppN(v___x_2870_, v___x_2872_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2873_);
return v___x_2874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2875_, lean_object* v_name_2876_, lean_object* v___y_2877_, lean_object* v___x_2878_, lean_object* v_levels_2879_, lean_object* v_params_2880_, lean_object* v_e_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2875_, v_name_2876_, v___y_2877_, v___x_2878_, v_levels_2879_, v_params_2880_, v_e_2881_);
lean_dec(v___x_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v_eqProof_2883_, lean_object* v___x_2884_, lean_object* v_eNew_2885_, lean_object* v_snd_2886_, lean_object* v___x_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___x_2893_; 
v___x_2893_ = l_Lean_Meta_mkEqMP(v_eqProof_2883_, v___x_2884_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2895_, 0, v_eNew_2885_);
v___x_2896_ = lean_box(0);
v___x_2897_ = l_Lean_MVarId_replace(v_snd_2886_, v___x_2887_, v_a_2894_, v___x_2895_, v___x_2896_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
return v___x_2897_;
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v___x_2887_);
lean_dec(v_snd_2886_);
lean_dec_ref(v_eNew_2885_);
v_a_2898_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2893_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2893_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object* v_eqProof_2906_, lean_object* v___x_2907_, lean_object* v_eNew_2908_, lean_object* v_snd_2909_, lean_object* v___x_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_2906_, v___x_2907_, v_eNew_2908_, v_snd_2909_, v___x_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2916_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; 
v___x_2918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0));
v___x_2919_ = l_Lean_stringToMessageData(v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9));
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_2943_, lean_object* v___x_2944_, lean_object* v___x_2945_, uint8_t v___x_2946_, lean_object* v___x_2947_, lean_object* v___x_2948_, uint8_t v___x_2949_, lean_object* v_params_2950_, lean_object* v_args_2951_, lean_object* v_indices_2952_, uint8_t v___x_2953_, lean_object* v_a_2954_, lean_object* v___x_2955_, lean_object* v___x_2956_, lean_object* v___f_2957_, lean_object* v___x_2958_, lean_object* v_targetArgs_2959_, lean_object* v_x_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; uint8_t v___x_2967_; 
v___x_2966_ = lean_array_get_size(v_targetArgs_2959_);
v___x_2967_ = lean_nat_dec_eq(v___x_2966_, v___x_2943_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v___x_2948_);
lean_dec(v___x_2947_);
lean_dec_ref(v___x_2945_);
v___x_2968_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_2969_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_2968_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_array_fget_borrowed(v_targetArgs_2959_, v___x_2944_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
lean_inc_ref(v___x_2945_);
v___x_2971_ = lean_infer_type(v___x_2945_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v_a_2972_; 
v_a_2972_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_a_2972_);
lean_dec_ref_known(v___x_2971_, 1);
if (lean_obj_tag(v_a_2972_) == 7)
{
lean_object* v_binderType_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v_binderType_2973_ = lean_ctor_get(v_a_2972_, 1);
lean_inc_ref(v_binderType_2973_);
lean_dec_ref_known(v_a_2972_, 3);
v___x_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2974_, 0, v_binderType_2973_);
v___x_2975_ = l_Lean_Meta_mkFreshExprMVar(v___x_2974_, v___x_2946_, v___x_2947_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc(v_a_2976_);
lean_dec_ref_known(v___x_2975_, 1);
v___x_2977_ = l_Lean_Expr_mvarId_x21(v_a_2976_);
v___x_2978_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2977_, v___x_2948_, v___x_2949_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
lean_inc(v___x_2970_);
v___x_2980_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2979_, v___x_2970_, v___y_2962_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3062_; 
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3062_ == 0)
{
lean_object* v_unused_3063_; 
v_unused_3063_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_3063_);
v___x_2982_ = v___x_2980_;
v_isShared_2983_ = v_isSharedCheck_3062_;
goto v_resetjp_2981_;
}
else
{
lean_dec(v___x_2980_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3062_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; uint8_t v___x_2988_; lean_object* v___x_2989_; 
v___x_2984_ = l_Lean_Expr_app___override(v___x_2945_, v_a_2976_);
lean_inc_ref(v_params_2950_);
v___x_2985_ = l_Array_append___redArg(v_params_2950_, v_args_2951_);
v___x_2986_ = l_Array_append___redArg(v___x_2985_, v_indices_2952_);
v___x_2987_ = l_Array_append___redArg(v___x_2986_, v_targetArgs_2959_);
v___x_2988_ = 1;
v___x_2989_ = l_Lean_Meta_mkLambdaFVars(v___x_2987_, v___x_2984_, v___x_2953_, v___x_2949_, v___x_2953_, v___x_2949_, v___x_2988_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec_ref(v___x_2987_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_2990_, v___y_2962_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v___x_2993_ = l_Lean_ConstantInfo_levelParams(v_a_2954_);
v___x_2994_ = l_Lean_mkCasesOnName(v___x_2955_);
v___x_2995_ = l_Lean_Meta_mkForallFVars(v_params_2950_, v___x_2956_, v___x_2953_, v___x_2949_, v___x_2949_, v___x_2988_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec_ref(v_params_2950_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2997_ = lean_box(0);
lean_inc(v___x_2994_);
v___x_2998_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_2994_, v___x_2993_, v_a_2996_, v_a_2992_, v___x_2997_, v___y_2964_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; lean_object* v___x_3001_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref_known(v___x_2998_, 1);
if (v_isShared_2983_ == 0)
{
lean_ctor_set_tag(v___x_2982_, 1);
lean_ctor_set(v___x_2982_, 0, v_a_2999_);
v___x_3001_ = v___x_2982_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_2999_);
v___x_3001_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_addDecl(v___x_3001_, v___x_2953_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_dec_ref_known(v___x_3002_, 1);
v___x_3003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8));
v___x_3004_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3004_, 0, v___x_2994_);
lean_closure_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_box(0);
v___x_3007_ = lean_box(1);
v___x_3008_ = lean_mk_empty_array_with_capacity(v___x_2944_);
v___x_3009_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3009_, 0, v___x_3005_);
lean_ctor_set(v___x_3009_, 1, v___x_3006_);
lean_ctor_set(v___x_3009_, 2, v___x_3005_);
lean_ctor_set(v___x_3009_, 3, v___f_2957_);
lean_ctor_set(v___x_3009_, 4, v___x_3007_);
lean_ctor_set(v___x_3009_, 5, v___x_3007_);
lean_ctor_set(v___x_3009_, 6, v___x_3005_);
lean_ctor_set(v___x_3009_, 7, v___x_3008_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8, v___x_2949_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 1, v___x_2949_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 2, v___x_2949_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 3, v___x_2949_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 4, v___x_2953_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 5, v___x_2953_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 6, v___x_2953_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 7, v___x_2953_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 8, v___x_2949_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 9, v___x_2953_);
lean_ctor_set_uint8(v___x_3009_, sizeof(void*)*8 + 10, v___x_2949_);
v___x_3010_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3010_, 0, v___x_2958_);
lean_ctor_set(v___x_3010_, 1, v___x_3007_);
lean_ctor_set(v___x_3010_, 2, v___x_3006_);
lean_ctor_set(v___x_3010_, 3, v___x_3006_);
lean_ctor_set(v___x_3010_, 4, v___x_3006_);
lean_ctor_set(v___x_3010_, 5, v___x_3007_);
lean_ctor_set(v___x_3010_, 6, v___x_3006_);
v___x_3011_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3004_, v___x_3009_, v___x_3010_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3020_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3020_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v_fst_3016_; lean_object* v___x_3018_; 
v_fst_3016_ = lean_ctor_get(v_a_3012_, 0);
lean_inc(v_fst_3016_);
lean_dec(v_a_3012_);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v_fst_3016_);
v___x_3018_ = v___x_3014_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_fst_3016_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
v_a_3021_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_3011_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_3011_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_dec(v___x_2994_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
return v___x_3002_;
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v___x_2994_);
lean_del_object(v___x_2982_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
v_a_3030_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2998_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2998_);
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
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec(v___x_2994_);
lean_dec(v___x_2993_);
lean_dec(v_a_2992_);
lean_del_object(v___x_2982_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
v_a_3038_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_2995_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_2995_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_del_object(v___x_2982_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
v_a_3046_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_2991_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_2991_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_del_object(v___x_2982_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
v_a_3054_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2989_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2989_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
else
{
lean_dec(v_a_2976_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v___x_2945_);
return v___x_2980_;
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_a_2976_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v___x_2945_);
v_a_3064_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2978_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2978_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v___x_2948_);
lean_dec_ref(v___x_2945_);
v_a_3072_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_2975_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_2975_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_dec(v_a_2972_);
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v___x_2948_);
lean_dec(v___x_2947_);
lean_dec_ref(v___x_2945_);
v___x_3080_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3081_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3080_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_3081_;
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v___x_2958_);
lean_dec_ref(v___f_2957_);
lean_dec_ref(v___x_2956_);
lean_dec(v___x_2955_);
lean_dec_ref(v_params_2950_);
lean_dec_ref(v___x_2948_);
lean_dec(v___x_2947_);
lean_dec_ref(v___x_2945_);
v_a_3082_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_2971_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_2971_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3090_ = _args[0];
lean_object* v___x_3091_ = _args[1];
lean_object* v___x_3092_ = _args[2];
lean_object* v___x_3093_ = _args[3];
lean_object* v___x_3094_ = _args[4];
lean_object* v___x_3095_ = _args[5];
lean_object* v___x_3096_ = _args[6];
lean_object* v_params_3097_ = _args[7];
lean_object* v_args_3098_ = _args[8];
lean_object* v_indices_3099_ = _args[9];
lean_object* v___x_3100_ = _args[10];
lean_object* v_a_3101_ = _args[11];
lean_object* v___x_3102_ = _args[12];
lean_object* v___x_3103_ = _args[13];
lean_object* v___f_3104_ = _args[14];
lean_object* v___x_3105_ = _args[15];
lean_object* v_targetArgs_3106_ = _args[16];
lean_object* v_x_3107_ = _args[17];
lean_object* v___y_3108_ = _args[18];
lean_object* v___y_3109_ = _args[19];
lean_object* v___y_3110_ = _args[20];
lean_object* v___y_3111_ = _args[21];
lean_object* v___y_3112_ = _args[22];
_start:
{
uint8_t v___x_16314__boxed_3113_; uint8_t v___x_16317__boxed_3114_; uint8_t v___x_16318__boxed_3115_; lean_object* v_res_3116_; 
v___x_16314__boxed_3113_ = lean_unbox(v___x_3093_);
v___x_16317__boxed_3114_ = lean_unbox(v___x_3096_);
v___x_16318__boxed_3115_ = lean_unbox(v___x_3100_);
v_res_3116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3090_, v___x_3091_, v___x_3092_, v___x_16314__boxed_3113_, v___x_3094_, v___x_3095_, v___x_16317__boxed_3114_, v_params_3097_, v_args_3098_, v_indices_3099_, v___x_16318__boxed_3115_, v_a_3101_, v___x_3102_, v___x_3103_, v___f_3104_, v___x_3105_, v_targetArgs_3106_, v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec_ref(v_x_3107_);
lean_dec_ref(v_targetArgs_3106_);
lean_dec_ref(v_a_3101_);
lean_dec_ref(v_indices_3099_);
lean_dec_ref(v_args_3098_);
lean_dec(v___x_3091_);
lean_dec(v___x_3090_);
return v_res_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, uint8_t v___x_3120_, lean_object* v___x_3121_, lean_object* v___x_3122_, uint8_t v___x_3123_, lean_object* v_params_3124_, lean_object* v_args_3125_, uint8_t v___x_3126_, lean_object* v_a_3127_, lean_object* v___x_3128_, lean_object* v___x_3129_, lean_object* v___f_3130_, lean_object* v___x_3131_, lean_object* v___x_3132_, lean_object* v_indices_3133_, lean_object* v_goalType_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___f_3144_; lean_object* v___x_3145_; 
v___x_3140_ = l_Lean_mkAppN(v___x_3117_, v_indices_3133_);
v___x_3141_ = lean_box(v___x_3120_);
v___x_3142_ = lean_box(v___x_3123_);
v___x_3143_ = lean_box(v___x_3126_);
v___f_3144_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 23, 16);
lean_closure_set(v___f_3144_, 0, v___x_3118_);
lean_closure_set(v___f_3144_, 1, v___x_3119_);
lean_closure_set(v___f_3144_, 2, v___x_3140_);
lean_closure_set(v___f_3144_, 3, v___x_3141_);
lean_closure_set(v___f_3144_, 4, v___x_3121_);
lean_closure_set(v___f_3144_, 5, v___x_3122_);
lean_closure_set(v___f_3144_, 6, v___x_3142_);
lean_closure_set(v___f_3144_, 7, v_params_3124_);
lean_closure_set(v___f_3144_, 8, v_args_3125_);
lean_closure_set(v___f_3144_, 9, v_indices_3133_);
lean_closure_set(v___f_3144_, 10, v___x_3143_);
lean_closure_set(v___f_3144_, 11, v_a_3127_);
lean_closure_set(v___f_3144_, 12, v___x_3128_);
lean_closure_set(v___f_3144_, 13, v___x_3129_);
lean_closure_set(v___f_3144_, 14, v___f_3130_);
lean_closure_set(v___f_3144_, 15, v___x_3131_);
v___x_3145_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3134_, v___x_3132_, v___f_3144_, v___x_3126_, v___x_3126_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3146_ = _args[0];
lean_object* v___x_3147_ = _args[1];
lean_object* v___x_3148_ = _args[2];
lean_object* v___x_3149_ = _args[3];
lean_object* v___x_3150_ = _args[4];
lean_object* v___x_3151_ = _args[5];
lean_object* v___x_3152_ = _args[6];
lean_object* v_params_3153_ = _args[7];
lean_object* v_args_3154_ = _args[8];
lean_object* v___x_3155_ = _args[9];
lean_object* v_a_3156_ = _args[10];
lean_object* v___x_3157_ = _args[11];
lean_object* v___x_3158_ = _args[12];
lean_object* v___f_3159_ = _args[13];
lean_object* v___x_3160_ = _args[14];
lean_object* v___x_3161_ = _args[15];
lean_object* v_indices_3162_ = _args[16];
lean_object* v_goalType_3163_ = _args[17];
lean_object* v___y_3164_ = _args[18];
lean_object* v___y_3165_ = _args[19];
lean_object* v___y_3166_ = _args[20];
lean_object* v___y_3167_ = _args[21];
lean_object* v___y_3168_ = _args[22];
_start:
{
uint8_t v___x_16650__boxed_3169_; uint8_t v___x_16653__boxed_3170_; uint8_t v___x_16654__boxed_3171_; lean_object* v_res_3172_; 
v___x_16650__boxed_3169_ = lean_unbox(v___x_3149_);
v___x_16653__boxed_3170_ = lean_unbox(v___x_3152_);
v___x_16654__boxed_3171_ = lean_unbox(v___x_3155_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3146_, v___x_3147_, v___x_3148_, v___x_16650__boxed_3169_, v___x_3150_, v___x_3151_, v___x_16653__boxed_3170_, v_params_3153_, v_args_3154_, v___x_16654__boxed_3171_, v_a_3156_, v___x_3157_, v___x_3158_, v___f_3159_, v___x_3160_, v___x_3161_, v_indices_3162_, v_goalType_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object* v___x_3173_, uint8_t v___x_3174_, lean_object* v_snd_3175_, lean_object* v___x_3176_, uint8_t v___x_3177_, lean_object* v___x_3178_, lean_object* v___x_3179_, lean_object* v_a_3180_, lean_object* v___x_3181_, lean_object* v___x_3182_, uint8_t v___x_3183_, lean_object* v___x_3184_, lean_object* v_params_3185_, lean_object* v_args_3186_, lean_object* v_a_3187_, lean_object* v___x_3188_, lean_object* v___x_3189_, lean_object* v___f_3190_, lean_object* v___x_3191_, lean_object* v___x_3192_, lean_object* v_numIndices_3193_, lean_object* v_goalType_3194_, lean_object* v___x_3195_, lean_object* v___x_3196_, lean_object* v_fst_3197_, lean_object* v___x_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_lctx_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v_lctx_3204_ = lean_ctor_get(v___y_3199_, 2);
lean_inc(v___x_3173_);
lean_inc_ref(v_lctx_3204_);
v___x_3205_ = l_Lean_LocalContext_get_x21(v_lctx_3204_, v___x_3173_);
v___x_3206_ = l_Lean_LocalDecl_type(v___x_3205_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = 2;
v___x_3208_ = lean_box(0);
v___x_3209_ = 0;
v___x_3210_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3210_, 0, v___x_3208_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*1, v___x_3207_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*1 + 1, v___x_3174_);
lean_ctor_set_uint8(v___x_3210_, sizeof(void*)*1 + 2, v___x_3209_);
lean_inc_ref(v___x_3176_);
lean_inc(v_snd_3175_);
v___x_3211_ = l_Lean_MVarId_rewrite(v_snd_3175_, v___x_3206_, v___x_3176_, v___x_3174_, v___x_3210_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v_a_3212_; lean_object* v_eNew_3213_; lean_object* v_eqProof_3214_; lean_object* v___x_3215_; lean_object* v___f_3216_; lean_object* v___x_3217_; 
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_a_3212_);
lean_dec_ref_known(v___x_3211_, 1);
v_eNew_3213_ = lean_ctor_get(v_a_3212_, 0);
lean_inc_ref(v_eNew_3213_);
v_eqProof_3214_ = lean_ctor_get(v_a_3212_, 1);
lean_inc_ref(v_eqProof_3214_);
lean_dec(v_a_3212_);
lean_inc(v___x_3173_);
v___x_3215_ = l_Lean_mkFVar(v___x_3173_);
lean_inc(v_snd_3175_);
v___f_3216_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3216_, 0, v_eqProof_3214_);
lean_closure_set(v___f_3216_, 1, v___x_3215_);
lean_closure_set(v___f_3216_, 2, v_eNew_3213_);
lean_closure_set(v___f_3216_, 3, v_snd_3175_);
lean_closure_set(v___f_3216_, 4, v___x_3173_);
v___x_3217_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3175_, v___f_3216_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___y_3220_; uint8_t v___x_3248_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3248_ = lean_nat_dec_lt(v___x_3195_, v___x_3196_);
if (v___x_3248_ == 0)
{
v___y_3220_ = v_fst_3197_;
goto v___jp_3219_;
}
else
{
lean_object* v_fvarId_3249_; lean_object* v_xs_x27_3250_; lean_object* v___x_3251_; 
v_fvarId_3249_ = lean_ctor_get(v_a_3218_, 0);
v_xs_x27_3250_ = lean_array_fset(v_fst_3197_, v___x_3195_, v___x_3198_);
lean_inc(v_fvarId_3249_);
v___x_3251_ = lean_array_fset(v_xs_x27_3250_, v___x_3195_, v_fvarId_3249_);
v___y_3220_ = v___x_3251_;
goto v___jp_3219_;
}
v___jp_3219_:
{
lean_object* v_mvarId_3221_; lean_object* v___x_3222_; 
v_mvarId_3221_ = lean_ctor_get(v_a_3218_, 1);
lean_inc(v_mvarId_3221_);
lean_dec(v_a_3218_);
v___x_3222_ = l_Lean_MVarId_revert(v_mvarId_3221_, v___y_3220_, v___x_3177_, v___x_3177_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v_snd_3224_; lean_object* v___x_3225_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___x_3222_, 1);
v_snd_3224_ = lean_ctor_get(v_a_3223_, 1);
lean_inc(v_snd_3224_);
lean_dec(v_a_3223_);
v___x_3225_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3224_, v___x_3178_, v___y_3200_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3238_; 
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v___x_3225_, 0);
lean_dec(v_unused_3239_);
v___x_3227_ = v___x_3225_;
v_isShared_3228_ = v_isSharedCheck_3238_;
goto v_resetjp_3226_;
}
else
{
lean_dec(v___x_3225_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3238_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___f_3233_; lean_object* v___x_3235_; 
v___x_3229_ = l_Lean_Expr_app___override(v___x_3179_, v_a_3180_);
v___x_3230_ = lean_box(v___x_3183_);
v___x_3231_ = lean_box(v___x_3174_);
v___x_3232_ = lean_box(v___x_3177_);
v___f_3233_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 23, 16);
lean_closure_set(v___f_3233_, 0, v___x_3229_);
lean_closure_set(v___f_3233_, 1, v___x_3181_);
lean_closure_set(v___f_3233_, 2, v___x_3182_);
lean_closure_set(v___f_3233_, 3, v___x_3230_);
lean_closure_set(v___f_3233_, 4, v___x_3184_);
lean_closure_set(v___f_3233_, 5, v___x_3176_);
lean_closure_set(v___f_3233_, 6, v___x_3231_);
lean_closure_set(v___f_3233_, 7, v_params_3185_);
lean_closure_set(v___f_3233_, 8, v_args_3186_);
lean_closure_set(v___f_3233_, 9, v___x_3232_);
lean_closure_set(v___f_3233_, 10, v_a_3187_);
lean_closure_set(v___f_3233_, 11, v___x_3188_);
lean_closure_set(v___f_3233_, 12, v___x_3189_);
lean_closure_set(v___f_3233_, 13, v___f_3190_);
lean_closure_set(v___f_3233_, 14, v___x_3191_);
lean_closure_set(v___f_3233_, 15, v___x_3192_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set_tag(v___x_3227_, 1);
lean_ctor_set(v___x_3227_, 0, v_numIndices_3193_);
v___x_3235_ = v___x_3227_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_numIndices_3193_);
v___x_3235_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; 
v___x_3236_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3194_, v___x_3235_, v___f_3233_, v___x_3177_, v___x_3177_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec_ref(v___y_3199_);
return v___x_3236_;
}
}
}
else
{
lean_dec_ref(v___y_3199_);
lean_dec_ref(v_goalType_3194_);
lean_dec(v_numIndices_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v___f_3190_);
lean_dec_ref(v___x_3189_);
lean_dec(v___x_3188_);
lean_dec_ref(v_a_3187_);
lean_dec_ref(v_args_3186_);
lean_dec_ref(v_params_3185_);
lean_dec(v___x_3184_);
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
lean_dec_ref(v_a_3180_);
lean_dec_ref(v___x_3179_);
lean_dec_ref(v___x_3176_);
return v___x_3225_;
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v___y_3199_);
lean_dec_ref(v_goalType_3194_);
lean_dec(v_numIndices_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v___f_3190_);
lean_dec_ref(v___x_3189_);
lean_dec(v___x_3188_);
lean_dec_ref(v_a_3187_);
lean_dec_ref(v_args_3186_);
lean_dec_ref(v_params_3185_);
lean_dec(v___x_3184_);
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
lean_dec_ref(v_a_3180_);
lean_dec_ref(v___x_3179_);
lean_dec_ref(v___x_3178_);
lean_dec_ref(v___x_3176_);
v_a_3240_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3222_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3222_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___y_3199_);
lean_dec_ref(v_fst_3197_);
lean_dec_ref(v_goalType_3194_);
lean_dec(v_numIndices_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v___f_3190_);
lean_dec_ref(v___x_3189_);
lean_dec(v___x_3188_);
lean_dec_ref(v_a_3187_);
lean_dec_ref(v_args_3186_);
lean_dec_ref(v_params_3185_);
lean_dec(v___x_3184_);
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
lean_dec_ref(v_a_3180_);
lean_dec_ref(v___x_3179_);
lean_dec_ref(v___x_3178_);
lean_dec_ref(v___x_3176_);
v_a_3252_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3217_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3217_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v___y_3199_);
lean_dec_ref(v_fst_3197_);
lean_dec_ref(v_goalType_3194_);
lean_dec(v_numIndices_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec_ref(v___f_3190_);
lean_dec_ref(v___x_3189_);
lean_dec(v___x_3188_);
lean_dec_ref(v_a_3187_);
lean_dec_ref(v_args_3186_);
lean_dec_ref(v_params_3185_);
lean_dec(v___x_3184_);
lean_dec(v___x_3182_);
lean_dec(v___x_3181_);
lean_dec_ref(v_a_3180_);
lean_dec_ref(v___x_3179_);
lean_dec_ref(v___x_3178_);
lean_dec_ref(v___x_3176_);
lean_dec(v_snd_3175_);
lean_dec(v___x_3173_);
v_a_3260_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3211_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3211_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object** _args){
lean_object* v___x_3268_ = _args[0];
lean_object* v___x_3269_ = _args[1];
lean_object* v_snd_3270_ = _args[2];
lean_object* v___x_3271_ = _args[3];
lean_object* v___x_3272_ = _args[4];
lean_object* v___x_3273_ = _args[5];
lean_object* v___x_3274_ = _args[6];
lean_object* v_a_3275_ = _args[7];
lean_object* v___x_3276_ = _args[8];
lean_object* v___x_3277_ = _args[9];
lean_object* v___x_3278_ = _args[10];
lean_object* v___x_3279_ = _args[11];
lean_object* v_params_3280_ = _args[12];
lean_object* v_args_3281_ = _args[13];
lean_object* v_a_3282_ = _args[14];
lean_object* v___x_3283_ = _args[15];
lean_object* v___x_3284_ = _args[16];
lean_object* v___f_3285_ = _args[17];
lean_object* v___x_3286_ = _args[18];
lean_object* v___x_3287_ = _args[19];
lean_object* v_numIndices_3288_ = _args[20];
lean_object* v_goalType_3289_ = _args[21];
lean_object* v___x_3290_ = _args[22];
lean_object* v___x_3291_ = _args[23];
lean_object* v_fst_3292_ = _args[24];
lean_object* v___x_3293_ = _args[25];
lean_object* v___y_3294_ = _args[26];
lean_object* v___y_3295_ = _args[27];
lean_object* v___y_3296_ = _args[28];
lean_object* v___y_3297_ = _args[29];
lean_object* v___y_3298_ = _args[30];
_start:
{
uint8_t v___x_16717__boxed_3299_; uint8_t v___x_16720__boxed_3300_; uint8_t v___x_16726__boxed_3301_; lean_object* v_res_3302_; 
v___x_16717__boxed_3299_ = lean_unbox(v___x_3269_);
v___x_16720__boxed_3300_ = lean_unbox(v___x_3272_);
v___x_16726__boxed_3301_ = lean_unbox(v___x_3278_);
v_res_3302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3268_, v___x_16717__boxed_3299_, v_snd_3270_, v___x_3271_, v___x_16720__boxed_3300_, v___x_3273_, v___x_3274_, v_a_3275_, v___x_3276_, v___x_3277_, v___x_16726__boxed_3301_, v___x_3279_, v_params_3280_, v_args_3281_, v_a_3282_, v___x_3283_, v___x_3284_, v___f_3285_, v___x_3286_, v___x_3287_, v_numIndices_3288_, v_goalType_3289_, v___x_3290_, v___x_3291_, v_fst_3292_, v___x_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v___y_3295_);
lean_dec(v___x_3291_);
lean_dec(v___x_3290_);
return v_res_3302_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t v___x_3303_, lean_object* v_x_3304_){
_start:
{
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object* v___x_3305_, lean_object* v_x_3306_){
_start:
{
uint8_t v___x_16916__boxed_3307_; uint8_t v_res_3308_; lean_object* v_r_3309_; 
v___x_16916__boxed_3307_ = lean_unbox(v___x_3305_);
v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_16916__boxed_3307_, v_x_3306_);
lean_dec(v_x_3306_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object* v___x_3313_, lean_object* v_a_3314_, lean_object* v___x_3315_, lean_object* v_numIndices_3316_, lean_object* v___x_3317_, lean_object* v___x_3318_, lean_object* v___x_3319_, lean_object* v_params_3320_, lean_object* v_a_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v_args_3326_, lean_object* v_goalType_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; uint8_t v___x_3334_; 
v___x_3333_ = lean_array_get_size(v_args_3326_);
v___x_3334_ = lean_nat_dec_eq(v___x_3333_, v___x_3313_);
if (v___x_3334_ == 0)
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
lean_dec_ref(v_goalType_3327_);
lean_dec_ref(v_args_3326_);
lean_dec(v___x_3324_);
lean_dec_ref(v___x_3323_);
lean_dec(v___x_3322_);
lean_dec_ref(v_a_3321_);
lean_dec_ref(v_params_3320_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3318_);
lean_dec(v_numIndices_3316_);
lean_dec(v___x_3315_);
lean_dec(v___x_3313_);
v___x_3335_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3336_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3335_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3336_;
}
else
{
if (lean_obj_tag(v_a_3314_) == 7)
{
lean_object* v_binderType_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_binderType_3337_ = lean_ctor_get(v_a_3314_, 1);
v___x_3338_ = lean_array_fget(v_args_3326_, v___x_3315_);
lean_inc_ref(v_binderType_3337_);
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v_binderType_3337_);
v___x_3340_ = 0;
v___x_3341_ = lean_box(0);
v___x_3342_ = l_Lean_Meta_mkFreshExprMVar(v___x_3339_, v___x_3340_, v___x_3341_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v_a_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___f_3348_; lean_object* v___x_3349_; 
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
lean_inc(v_a_3343_);
lean_dec_ref_known(v___x_3342_, 1);
v___x_3344_ = l_Lean_Expr_mvarId_x21(v_a_3343_);
v___x_3345_ = lean_nat_add(v_numIndices_3316_, v___x_3313_);
v___x_3346_ = lean_box(0);
v___x_3347_ = 0;
v___f_3348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0));
v___x_3349_ = l_Lean_Meta_introNCore(v___x_3344_, v___x_3345_, v___x_3346_, v___x_3347_, v___x_3347_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v_fst_3351_; lean_object* v_snd_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___f_3359_; lean_object* v___x_3360_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
v_fst_3351_ = lean_ctor_get(v_a_3350_, 0);
lean_inc(v_fst_3351_);
v_snd_3352_ = lean_ctor_get(v_a_3350_, 1);
lean_inc_n(v_snd_3352_, 2);
lean_dec(v_a_3350_);
v___x_3353_ = lean_array_get_size(v_fst_3351_);
v___x_3354_ = lean_nat_sub(v___x_3353_, v___x_3313_);
v___x_3355_ = lean_array_get(v___x_3317_, v_fst_3351_, v___x_3354_);
v___x_3356_ = lean_box(v___x_3334_);
v___x_3357_ = lean_box(v___x_3347_);
v___x_3358_ = lean_box(v___x_3340_);
v___f_3359_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed), 31, 26);
lean_closure_set(v___f_3359_, 0, v___x_3355_);
lean_closure_set(v___f_3359_, 1, v___x_3356_);
lean_closure_set(v___f_3359_, 2, v_snd_3352_);
lean_closure_set(v___f_3359_, 3, v___x_3318_);
lean_closure_set(v___f_3359_, 4, v___x_3357_);
lean_closure_set(v___f_3359_, 5, v___x_3338_);
lean_closure_set(v___f_3359_, 6, v___x_3319_);
lean_closure_set(v___f_3359_, 7, v_a_3343_);
lean_closure_set(v___f_3359_, 8, v___x_3313_);
lean_closure_set(v___f_3359_, 9, v___x_3315_);
lean_closure_set(v___f_3359_, 10, v___x_3358_);
lean_closure_set(v___f_3359_, 11, v___x_3341_);
lean_closure_set(v___f_3359_, 12, v_params_3320_);
lean_closure_set(v___f_3359_, 13, v_args_3326_);
lean_closure_set(v___f_3359_, 14, v_a_3321_);
lean_closure_set(v___f_3359_, 15, v___x_3322_);
lean_closure_set(v___f_3359_, 16, v___x_3323_);
lean_closure_set(v___f_3359_, 17, v___f_3348_);
lean_closure_set(v___f_3359_, 18, v___x_3346_);
lean_closure_set(v___f_3359_, 19, v___x_3324_);
lean_closure_set(v___f_3359_, 20, v_numIndices_3316_);
lean_closure_set(v___f_3359_, 21, v_goalType_3327_);
lean_closure_set(v___f_3359_, 22, v___x_3354_);
lean_closure_set(v___f_3359_, 23, v___x_3353_);
lean_closure_set(v___f_3359_, 24, v_fst_3351_);
lean_closure_set(v___f_3359_, 25, v___x_3325_);
v___x_3360_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3352_, v___f_3359_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3360_;
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3343_);
lean_dec(v___x_3338_);
lean_dec_ref(v_goalType_3327_);
lean_dec_ref(v_args_3326_);
lean_dec(v___x_3324_);
lean_dec_ref(v___x_3323_);
lean_dec(v___x_3322_);
lean_dec_ref(v_a_3321_);
lean_dec_ref(v_params_3320_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3318_);
lean_dec(v_numIndices_3316_);
lean_dec(v___x_3315_);
lean_dec(v___x_3313_);
v_a_3361_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3349_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3349_);
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
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v___x_3338_);
lean_dec_ref(v_goalType_3327_);
lean_dec_ref(v_args_3326_);
lean_dec(v___x_3324_);
lean_dec_ref(v___x_3323_);
lean_dec(v___x_3322_);
lean_dec_ref(v_a_3321_);
lean_dec_ref(v_params_3320_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3318_);
lean_dec(v_numIndices_3316_);
lean_dec(v___x_3315_);
lean_dec(v___x_3313_);
v_a_3369_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3342_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3342_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
lean_dec_ref(v_goalType_3327_);
lean_dec_ref(v_args_3326_);
lean_dec(v___x_3324_);
lean_dec_ref(v___x_3323_);
lean_dec(v___x_3322_);
lean_dec_ref(v_a_3321_);
lean_dec_ref(v_params_3320_);
lean_dec_ref(v___x_3319_);
lean_dec_ref(v___x_3318_);
lean_dec(v_numIndices_3316_);
lean_dec(v___x_3315_);
lean_dec(v___x_3313_);
v___x_3377_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3378_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3377_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3378_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object** _args){
lean_object* v___x_3379_ = _args[0];
lean_object* v_a_3380_ = _args[1];
lean_object* v___x_3381_ = _args[2];
lean_object* v_numIndices_3382_ = _args[3];
lean_object* v___x_3383_ = _args[4];
lean_object* v___x_3384_ = _args[5];
lean_object* v___x_3385_ = _args[6];
lean_object* v_params_3386_ = _args[7];
lean_object* v_a_3387_ = _args[8];
lean_object* v___x_3388_ = _args[9];
lean_object* v___x_3389_ = _args[10];
lean_object* v___x_3390_ = _args[11];
lean_object* v___x_3391_ = _args[12];
lean_object* v_args_3392_ = _args[13];
lean_object* v_goalType_3393_ = _args[14];
lean_object* v___y_3394_ = _args[15];
lean_object* v___y_3395_ = _args[16];
lean_object* v___y_3396_ = _args[17];
lean_object* v___y_3397_ = _args[18];
lean_object* v___y_3398_ = _args[19];
_start:
{
lean_object* v_res_3399_; 
v_res_3399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3379_, v_a_3380_, v___x_3381_, v_numIndices_3382_, v___x_3383_, v___x_3384_, v___x_3385_, v_params_3386_, v_a_3387_, v___x_3388_, v___x_3389_, v___x_3390_, v___x_3391_, v_args_3392_, v_goalType_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___x_3383_);
lean_dec_ref(v_a_3380_);
return v_res_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v___x_3406_; lean_object* v_env_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; 
v___x_3406_ = lean_st_ref_get(v___y_3404_);
v_env_3407_ = lean_ctor_get(v___x_3406_, 0);
lean_inc_ref(v_env_3407_);
lean_dec(v___x_3406_);
v___x_3408_ = 0;
lean_inc(v_constName_3400_);
v___x_3409_ = l_Lean_Environment_findConstVal_x3f(v_env_3407_, v_constName_3400_, v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
return v___x_3410_;
}
else
{
lean_object* v_val_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec(v_constName_3400_);
v_val_3411_ = lean_ctor_get(v___x_3409_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3409_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3409_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_val_3411_);
lean_dec(v___x_3409_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set_tag(v___x_3413_, 0);
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_val_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3432_; 
lean_inc(v_constName_3426_);
v___x_3432_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3444_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3444_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v_levelParams_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3442_; 
v_levelParams_3437_ = lean_ctor_get(v_a_3433_, 1);
lean_inc(v_levelParams_3437_);
lean_dec(v_a_3433_);
v___x_3438_ = lean_box(0);
v___x_3439_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3437_, v___x_3438_);
v___x_3440_ = l_Lean_mkConst(v_constName_3426_, v___x_3439_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3440_);
v___x_3442_ = v___x_3435_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec(v_constName_3426_);
v_a_3445_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3432_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3432_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v___y_3462_, lean_object* v_levels_3463_, lean_object* v_params_3464_, lean_object* v_predicates_3465_, lean_object* v_as_3466_, size_t v_sz_3467_, size_t v_i_3468_, lean_object* v_b_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
uint8_t v___x_3475_; 
v___x_3475_ = lean_usize_dec_lt(v_i_3468_, v_sz_3467_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; 
lean_dec_ref(v_params_3464_);
lean_dec(v_levels_3463_);
lean_dec_ref(v___y_3462_);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v_b_3469_);
return v___x_3476_;
}
else
{
lean_object* v_a_3477_; lean_object* v_toConstantVal_3478_; lean_object* v_numParams_3479_; lean_object* v_numIndices_3480_; lean_object* v_name_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___f_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v_a_3477_ = lean_array_uget_borrowed(v_as_3466_, v_i_3468_);
v_toConstantVal_3478_ = lean_ctor_get(v_a_3477_, 0);
v_numParams_3479_ = lean_ctor_get(v_a_3477_, 1);
v_numIndices_3480_ = lean_ctor_get(v_a_3477_, 2);
v_name_3481_ = lean_ctor_get(v_toConstantVal_3478_, 0);
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = lean_box(0);
v___x_3484_ = lean_box(0);
lean_inc_ref(v_params_3464_);
lean_inc(v_levels_3463_);
lean_inc_ref(v___y_3462_);
lean_inc_n(v_name_3481_, 2);
lean_inc(v_numParams_3479_);
v___f_3485_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3485_, 0, v_numParams_3479_);
lean_closure_set(v___f_3485_, 1, v_name_3481_);
lean_closure_set(v___f_3485_, 2, v___y_3462_);
lean_closure_set(v___f_3485_, 3, v___x_3482_);
lean_closure_set(v___f_3485_, 4, v_levels_3463_);
lean_closure_set(v___f_3485_, 5, v_params_3464_);
v___x_3486_ = l_Lean_mkCasesOnName(v_name_3481_);
lean_inc(v___x_3486_);
v___x_3487_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3486_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
v___x_3489_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3486_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
lean_inc_ref(v_params_3464_);
v___x_3491_ = l_Array_append___redArg(v_params_3464_, v_predicates_3465_);
v___x_3492_ = l_Lean_mkAppN(v_a_3490_, v___x_3491_);
lean_dec_ref(v___x_3491_);
lean_inc(v___y_3473_);
lean_inc_ref(v___y_3472_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc_ref(v___x_3492_);
v___x_3493_ = lean_infer_type(v___x_3492_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
v___x_3495_ = lean_replace_expr(v___f_3485_, v_a_3494_);
lean_dec(v_a_3494_);
lean_dec_ref(v___f_3485_);
lean_inc(v___y_3473_);
lean_inc_ref(v___y_3472_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc_ref(v___x_3492_);
v___x_3496_ = lean_infer_type(v___x_3492_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___f_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
lean_inc(v_name_3481_);
v___x_3498_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3481_);
v___x_3499_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3498_);
v___x_3500_ = l_Lean_Name_append(v___x_3498_, v___x_3499_);
lean_inc(v_levels_3463_);
v___x_3501_ = l_Lean_mkConst(v___x_3500_, v_levels_3463_);
v___x_3502_ = lean_unsigned_to_nat(1u);
v___x_3503_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3495_);
lean_inc_ref(v_params_3464_);
lean_inc(v_numIndices_3480_);
v___f_3504_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed), 20, 13);
lean_closure_set(v___f_3504_, 0, v___x_3502_);
lean_closure_set(v___f_3504_, 1, v_a_3497_);
lean_closure_set(v___f_3504_, 2, v___x_3482_);
lean_closure_set(v___f_3504_, 3, v_numIndices_3480_);
lean_closure_set(v___f_3504_, 4, v___x_3483_);
lean_closure_set(v___f_3504_, 5, v___x_3501_);
lean_closure_set(v___f_3504_, 6, v___x_3492_);
lean_closure_set(v___f_3504_, 7, v_params_3464_);
lean_closure_set(v___f_3504_, 8, v_a_3488_);
lean_closure_set(v___f_3504_, 9, v___x_3498_);
lean_closure_set(v___f_3504_, 10, v___x_3495_);
lean_closure_set(v___f_3504_, 11, v___x_3503_);
lean_closure_set(v___f_3504_, 12, v___x_3484_);
v___x_3505_ = 0;
v___x_3506_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_3495_, v___x_3503_, v___f_3504_, v___x_3505_, v___x_3505_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3506_) == 0)
{
size_t v___x_3507_; size_t v___x_3508_; 
lean_dec_ref_known(v___x_3506_, 1);
v___x_3507_ = ((size_t)1ULL);
v___x_3508_ = lean_usize_add(v_i_3468_, v___x_3507_);
v_i_3468_ = v___x_3508_;
v_b_3469_ = v___x_3484_;
goto _start;
}
else
{
lean_dec_ref(v_params_3464_);
lean_dec(v_levels_3463_);
lean_dec_ref(v___y_3462_);
return v___x_3506_;
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v___x_3495_);
lean_dec_ref(v___x_3492_);
lean_dec(v_a_3488_);
lean_dec_ref(v_params_3464_);
lean_dec(v_levels_3463_);
lean_dec_ref(v___y_3462_);
v_a_3510_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3496_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3496_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec_ref(v___x_3492_);
lean_dec(v_a_3488_);
lean_dec_ref(v___f_3485_);
lean_dec_ref(v_params_3464_);
lean_dec(v_levels_3463_);
lean_dec_ref(v___y_3462_);
v_a_3518_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3493_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3493_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3523_; 
if (v_isShared_3521_ == 0)
{
v___x_3523_ = v___x_3520_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v_a_3488_);
lean_dec_ref(v___f_3485_);
lean_dec_ref(v_params_3464_);
lean_dec(v_levels_3463_);
lean_dec_ref(v___y_3462_);
v_a_3526_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3489_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3489_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec(v___x_3486_);
lean_dec_ref(v___f_3485_);
lean_dec_ref(v_params_3464_);
lean_dec(v_levels_3463_);
lean_dec_ref(v___y_3462_);
v_a_3534_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3487_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3487_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v___y_3542_, lean_object* v_levels_3543_, lean_object* v_params_3544_, lean_object* v_predicates_3545_, lean_object* v_as_3546_, lean_object* v_sz_3547_, lean_object* v_i_3548_, lean_object* v_b_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
size_t v_sz_boxed_3555_; size_t v_i_boxed_3556_; lean_object* v_res_3557_; 
v_sz_boxed_3555_ = lean_unbox_usize(v_sz_3547_);
lean_dec(v_sz_3547_);
v_i_boxed_3556_ = lean_unbox_usize(v_i_3548_);
lean_dec(v_i_3548_);
v_res_3557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3542_, v_levels_3543_, v_params_3544_, v_predicates_3545_, v_as_3546_, v_sz_boxed_3555_, v_i_boxed_3556_, v_b_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v_as_3546_);
lean_dec_ref(v_predicates_3545_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3558_, size_t v_sz_3559_, size_t v_i_3560_, lean_object* v_bs_3561_){
_start:
{
uint8_t v___x_3562_; 
v___x_3562_ = lean_usize_dec_lt(v_i_3560_, v_sz_3559_);
if (v___x_3562_ == 0)
{
lean_dec(v_levels_3558_);
return v_bs_3561_;
}
else
{
lean_object* v_v_3563_; lean_object* v_toConstantVal_3564_; lean_object* v_name_3565_; lean_object* v___x_3566_; lean_object* v_bs_x27_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; size_t v___x_3570_; size_t v___x_3571_; lean_object* v___x_3572_; 
v_v_3563_ = lean_array_uget_borrowed(v_bs_3561_, v_i_3560_);
v_toConstantVal_3564_ = lean_ctor_get(v_v_3563_, 0);
v_name_3565_ = lean_ctor_get(v_toConstantVal_3564_, 0);
lean_inc(v_name_3565_);
v___x_3566_ = lean_unsigned_to_nat(0u);
v_bs_x27_3567_ = lean_array_uset(v_bs_3561_, v_i_3560_, v___x_3566_);
v___x_3568_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3565_);
lean_inc(v_levels_3558_);
v___x_3569_ = l_Lean_mkConst(v___x_3568_, v_levels_3558_);
v___x_3570_ = ((size_t)1ULL);
v___x_3571_ = lean_usize_add(v_i_3560_, v___x_3570_);
v___x_3572_ = lean_array_uset(v_bs_x27_3567_, v_i_3560_, v___x_3569_);
v_i_3560_ = v___x_3571_;
v_bs_3561_ = v___x_3572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3574_, lean_object* v_sz_3575_, lean_object* v_i_3576_, lean_object* v_bs_3577_){
_start:
{
size_t v_sz_boxed_3578_; size_t v_i_boxed_3579_; lean_object* v_res_3580_; 
v_sz_boxed_3578_ = lean_unbox_usize(v_sz_3575_);
lean_dec(v_sz_3575_);
v_i_boxed_3579_ = lean_unbox_usize(v_i_3576_);
lean_dec(v_i_3576_);
v_res_3580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3574_, v_sz_boxed_3578_, v_i_boxed_3579_, v_bs_3577_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3581_, lean_object* v_levels_3582_, lean_object* v___y_3583_, lean_object* v_params_3584_, lean_object* v_x_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
size_t v_sz_3591_; size_t v___x_3592_; lean_object* v_predicates_3593_; size_t v_sz_3594_; lean_object* v_predicates_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v_sz_3591_ = lean_array_size(v_infos_3581_);
v___x_3592_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3581_);
lean_inc(v_levels_3582_);
v_predicates_3593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3582_, v_sz_3591_, v___x_3592_, v_infos_3581_);
v_sz_3594_ = lean_array_size(v_predicates_3593_);
v_predicates_3595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3584_, v_sz_3594_, v___x_3592_, v_predicates_3593_);
v___x_3596_ = lean_box(0);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3583_, v_levels_3582_, v_params_3584_, v_predicates_3595_, v_infos_3581_, v_sz_3591_, v___x_3592_, v___x_3596_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_);
lean_dec_ref(v_infos_3581_);
lean_dec_ref(v_predicates_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3604_ == 0)
{
lean_object* v_unused_3605_; 
v_unused_3605_ = lean_ctor_get(v___x_3597_, 0);
lean_dec(v_unused_3605_);
v___x_3599_ = v___x_3597_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_dec(v___x_3597_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 0, v___x_3596_);
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3596_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
else
{
return v___x_3597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3606_, lean_object* v_levels_3607_, lean_object* v___y_3608_, lean_object* v_params_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3606_, v_levels_3607_, v___y_3608_, v_params_3609_, v_x_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_x_3610_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3617_, size_t v_i_3618_, size_t v_stop_3619_, lean_object* v_b_3620_){
_start:
{
uint8_t v___x_3621_; 
v___x_3621_ = lean_usize_dec_eq(v_i_3618_, v_stop_3619_);
if (v___x_3621_ == 0)
{
lean_object* v___x_3622_; lean_object* v_ctors_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; size_t v___x_3626_; size_t v___x_3627_; 
v___x_3622_ = lean_array_uget_borrowed(v_as_3617_, v_i_3618_);
v_ctors_3623_ = lean_ctor_get(v___x_3622_, 4);
lean_inc(v_ctors_3623_);
v___x_3624_ = lean_array_mk(v_ctors_3623_);
v___x_3625_ = l_Array_append___redArg(v_b_3620_, v___x_3624_);
lean_dec_ref(v___x_3624_);
v___x_3626_ = ((size_t)1ULL);
v___x_3627_ = lean_usize_add(v_i_3618_, v___x_3626_);
v_i_3618_ = v___x_3627_;
v_b_3620_ = v___x_3625_;
goto _start;
}
else
{
return v_b_3620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3629_, lean_object* v_i_3630_, lean_object* v_stop_3631_, lean_object* v_b_3632_){
_start:
{
size_t v_i_boxed_3633_; size_t v_stop_boxed_3634_; lean_object* v_res_3635_; 
v_i_boxed_3633_ = lean_unbox_usize(v_i_3630_);
lean_dec(v_i_3630_);
v_stop_boxed_3634_ = lean_unbox_usize(v_stop_3631_);
lean_dec(v_stop_3631_);
v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3629_, v_i_boxed_3633_, v_stop_boxed_3634_, v_b_3632_);
lean_dec_ref(v_as_3629_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v_toConstantVal_3647_; lean_object* v_numParams_3648_; lean_object* v_levelParams_3649_; lean_object* v_type_3650_; lean_object* v___x_3651_; lean_object* v_levels_3652_; lean_object* v___y_3654_; lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3644_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3645_ = lean_unsigned_to_nat(0u);
v___x_3646_ = lean_array_get_borrowed(v___x_3644_, v_infos_3638_, v___x_3645_);
v_toConstantVal_3647_ = lean_ctor_get(v___x_3646_, 0);
v_numParams_3648_ = lean_ctor_get(v___x_3646_, 1);
lean_inc(v_numParams_3648_);
v_levelParams_3649_ = lean_ctor_get(v_toConstantVal_3647_, 1);
v_type_3650_ = lean_ctor_get(v_toConstantVal_3647_, 2);
lean_inc_ref(v_type_3650_);
v___x_3651_ = lean_box(0);
lean_inc(v_levelParams_3649_);
v_levels_3652_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3649_, v___x_3651_);
v___x_3661_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3662_ = lean_array_get_size(v_infos_3638_);
v___x_3663_ = lean_nat_dec_lt(v___x_3645_, v___x_3662_);
if (v___x_3663_ == 0)
{
v___y_3654_ = v___x_3661_;
goto v___jp_3653_;
}
else
{
size_t v___x_3664_; size_t v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = ((size_t)0ULL);
v___x_3665_ = lean_usize_of_nat(v___x_3662_);
v___x_3666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3638_, v___x_3664_, v___x_3665_, v___x_3661_);
v___y_3654_ = v___x_3666_;
goto v___jp_3653_;
}
v___jp_3653_:
{
lean_object* v___f_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; 
lean_inc_ref(v_infos_3638_);
v___f_3655_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3655_, 0, v_infos_3638_);
lean_closure_set(v___f_3655_, 1, v_levels_3652_);
lean_closure_set(v___f_3655_, 2, v___y_3654_);
v___x_3656_ = lean_array_get_size(v_infos_3638_);
lean_dec_ref(v_infos_3638_);
v___x_3657_ = lean_nat_sub(v_numParams_3648_, v___x_3656_);
lean_dec(v_numParams_3648_);
v___x_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
v___x_3659_ = 0;
v___x_3660_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_3650_, v___x_3658_, v___f_3655_, v___x_3659_, v___x_3659_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_);
return v___x_3660_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v_res_3673_; 
v_res_3673_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3674_, lean_object* v_constName_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3682_, lean_object* v_constName_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3682_, v_constName_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3690_, lean_object* v_ref_3691_, lean_object* v_constName_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; 
v___x_3698_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3691_, v_constName_3692_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3699_, lean_object* v_ref_3700_, lean_object* v_constName_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3699_, v_ref_3700_, v_constName_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v_ref_3700_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3708_, lean_object* v_ref_3709_, lean_object* v_msg_3710_, lean_object* v_declHint_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3709_, v_msg_3710_, v_declHint_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3718_, lean_object* v_ref_3719_, lean_object* v_msg_3720_, lean_object* v_declHint_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3718_, v_ref_3719_, v_msg_3720_, v_declHint_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v_ref_3719_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3728_, lean_object* v_declHint_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3735_; 
v___x_3735_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3728_, v_declHint_3729_, v___y_3733_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3736_, lean_object* v_declHint_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3736_, v_declHint_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3744_, lean_object* v_ref_3745_, lean_object* v_msg_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; 
v___x_3752_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3745_, v_msg_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3753_, lean_object* v_ref_3754_, lean_object* v_msg_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3753_, v_ref_3754_, v_msg_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v_ref_3754_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3765_, lean_object* v___x_3766_, lean_object* v_params_3767_, size_t v_sz_3768_, size_t v_i_3769_, lean_object* v_bs_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
uint8_t v___x_3776_; 
v___x_3776_ = lean_usize_dec_lt(v_i_3769_, v_sz_3768_);
if (v___x_3776_ == 0)
{
lean_object* v___x_3777_; 
lean_dec_ref(v_params_3767_);
lean_dec_ref(v___x_3766_);
lean_dec(v___x_3765_);
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v_bs_3770_);
return v___x_3777_;
}
else
{
lean_object* v_v_3778_; lean_object* v_toConstantVal_3779_; lean_object* v_name_3780_; lean_object* v___x_3781_; lean_object* v_bs_x27_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_v_3778_ = lean_array_uget_borrowed(v_bs_3770_, v_i_3769_);
v_toConstantVal_3779_ = lean_ctor_get(v_v_3778_, 0);
v_name_3780_ = lean_ctor_get(v_toConstantVal_3779_, 0);
lean_inc(v_name_3780_);
v___x_3781_ = lean_unsigned_to_nat(0u);
v_bs_x27_3782_ = lean_array_uset(v_bs_3770_, v_i_3769_, v___x_3781_);
v___x_3783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3784_ = l_Lean_Name_append(v_name_3780_, v___x_3783_);
lean_inc(v___x_3765_);
v___x_3785_ = l_Lean_mkConst(v___x_3784_, v___x_3765_);
v___x_3786_ = l_Lean_Meta_unfoldDefinition(v___x_3785_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; size_t v_sz_3788_; size_t v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; uint8_t v___x_3794_; lean_object* v___x_3795_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3786_, 1);
v_sz_3788_ = lean_array_size(v___x_3766_);
v___x_3789_ = ((size_t)0ULL);
lean_inc_ref(v___x_3766_);
v___x_3790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3767_, v_sz_3788_, v___x_3789_, v___x_3766_);
lean_inc_ref(v_params_3767_);
v___x_3791_ = l_Array_append___redArg(v_params_3767_, v___x_3790_);
lean_dec_ref(v___x_3790_);
v___x_3792_ = l_Lean_mkAppN(v_a_3787_, v___x_3791_);
lean_dec_ref(v___x_3791_);
v___x_3793_ = 0;
v___x_3794_ = 1;
v___x_3795_ = l_Lean_Meta_mkLambdaFVars(v_params_3767_, v___x_3792_, v___x_3793_, v___x_3776_, v___x_3793_, v___x_3776_, v___x_3794_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; size_t v___x_3797_; size_t v___x_3798_; lean_object* v___x_3799_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v___x_3797_ = ((size_t)1ULL);
v___x_3798_ = lean_usize_add(v_i_3769_, v___x_3797_);
v___x_3799_ = lean_array_uset(v_bs_x27_3782_, v_i_3769_, v_a_3796_);
v_i_3769_ = v___x_3798_;
v_bs_3770_ = v___x_3799_;
goto _start;
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v_bs_x27_3782_);
lean_dec_ref(v_params_3767_);
lean_dec_ref(v___x_3766_);
lean_dec(v___x_3765_);
v_a_3801_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3795_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3795_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
else
{
lean_object* v_a_3809_; lean_object* v___x_3811_; uint8_t v_isShared_3812_; uint8_t v_isSharedCheck_3816_; 
lean_dec_ref(v_bs_x27_3782_);
lean_dec_ref(v_params_3767_);
lean_dec_ref(v___x_3766_);
lean_dec(v___x_3765_);
v_a_3809_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3816_ == 0)
{
v___x_3811_ = v___x_3786_;
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
else
{
lean_inc(v_a_3809_);
lean_dec(v___x_3786_);
v___x_3811_ = lean_box(0);
v_isShared_3812_ = v_isSharedCheck_3816_;
goto v_resetjp_3810_;
}
v_resetjp_3810_:
{
lean_object* v___x_3814_; 
if (v_isShared_3812_ == 0)
{
v___x_3814_ = v___x_3811_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v_params_3819_, lean_object* v_sz_3820_, lean_object* v_i_3821_, lean_object* v_bs_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
size_t v_sz_boxed_3828_; size_t v_i_boxed_3829_; lean_object* v_res_3830_; 
v_sz_boxed_3828_ = lean_unbox_usize(v_sz_3820_);
lean_dec(v_sz_3820_);
v_i_boxed_3829_ = lean_unbox_usize(v_i_3821_);
lean_dec(v_i_3821_);
v_res_3830_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3817_, v___x_3818_, v_params_3819_, v_sz_boxed_3828_, v_i_boxed_3829_, v_bs_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3831_, lean_object* v___x_3832_, size_t v_sz_3833_, size_t v___x_3834_, lean_object* v_a_3835_, lean_object* v_params_3836_, lean_object* v_x_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
lean_object* v___x_3845_; 
v___x_3845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3831_, v___x_3832_, v_params_3836_, v_sz_3833_, v___x_3834_, v_a_3835_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
return v___x_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3846_, lean_object* v___x_3847_, lean_object* v_sz_3848_, lean_object* v___x_3849_, lean_object* v_a_3850_, lean_object* v_params_3851_, lean_object* v_x_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
size_t v_sz_boxed_3860_; size_t v___x_5774__boxed_3861_; lean_object* v_res_3862_; 
v_sz_boxed_3860_ = lean_unbox_usize(v_sz_3848_);
lean_dec(v_sz_3848_);
v___x_5774__boxed_3861_ = lean_unbox_usize(v___x_3849_);
lean_dec(v___x_3849_);
v_res_3862_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3846_, v___x_3847_, v_sz_boxed_3860_, v___x_5774__boxed_3861_, v_a_3850_, v_params_3851_, v_x_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec_ref(v_x_3852_);
return v_res_3862_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(lean_object* v___x_3863_, uint8_t v___x_3864_, lean_object* v_attr_3865_){
_start:
{
lean_object* v_name_3866_; lean_object* v___x_3867_; 
v_name_3866_ = lean_ctor_get(v_attr_3865_, 0);
lean_inc(v_name_3866_);
lean_dec_ref(v_attr_3865_);
v___x_3867_ = l_Lean_getAttributeImpl(v___x_3863_, v_name_3866_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_dec_ref_known(v___x_3867_, 1);
return v___x_3864_;
}
else
{
lean_object* v_a_3868_; lean_object* v_toAttributeImplCore_3869_; uint8_t v_applicationTime_3870_; uint8_t v___x_3871_; uint8_t v___x_3872_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
v_toAttributeImplCore_3869_ = lean_ctor_get(v_a_3868_, 0);
lean_inc_ref(v_toAttributeImplCore_3869_);
lean_dec(v_a_3868_);
v_applicationTime_3870_ = lean_ctor_get_uint8(v_toAttributeImplCore_3869_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_3869_);
v___x_3871_ = 1;
v___x_3872_ = l_Lean_instBEqAttributeApplicationTime_beq(v_applicationTime_3870_, v___x_3871_);
if (v___x_3872_ == 0)
{
return v___x_3864_;
}
else
{
uint8_t v___x_3873_; 
v___x_3873_ = 0;
return v___x_3873_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed(lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v_attr_3876_){
_start:
{
uint8_t v___x_5811__boxed_3877_; uint8_t v_res_3878_; lean_object* v_r_3879_; 
v___x_5811__boxed_3877_ = lean_unbox(v___x_3875_);
v_res_3878_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(v___x_3874_, v___x_5811__boxed_3877_, v_attr_3876_);
v_r_3879_ = lean_box(v_res_3878_);
return v_r_3879_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = l_Lean_instInhabitedExpr;
v___x_3881_ = lean_box(0);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v___x_3880_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3883_, lean_object* v___x_3884_, lean_object* v_a_3885_, lean_object* v___x_3886_, size_t v_sz_3887_, size_t v_i_3888_, lean_object* v_bs_3889_){
_start:
{
uint8_t v___x_3890_; 
v___x_3890_ = lean_usize_dec_lt(v_i_3888_, v_sz_3887_);
if (v___x_3890_ == 0)
{
lean_dec(v___x_3886_);
lean_dec_ref(v___x_3884_);
return v_bs_3889_;
}
else
{
lean_object* v___x_3891_; lean_object* v_v_3892_; lean_object* v___x_3893_; lean_object* v_bs_x27_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v_modifiers_3897_; lean_object* v_ref_3898_; uint8_t v_isGreatest_3899_; lean_object* v_monotonicity_x3f_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3942_; 
v___x_3891_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v_v_3892_ = lean_array_uget(v_bs_3889_, v_i_3888_);
v___x_3893_ = lean_unsigned_to_nat(0u);
v_bs_x27_3894_ = lean_array_uset(v_bs_3889_, v_i_3888_, v___x_3893_);
v___x_3895_ = lean_usize_to_nat(v_i_3888_);
v___x_3896_ = lean_array_get(v___x_3891_, v_coinductiveElabData_3883_, v___x_3895_);
v_modifiers_3897_ = lean_ctor_get(v___x_3896_, 3);
v_ref_3898_ = lean_ctor_get(v___x_3896_, 2);
v_isGreatest_3899_ = lean_ctor_get_uint8(v___x_3896_, sizeof(void*)*6);
v_monotonicity_x3f_3900_ = lean_ctor_get(v___x_3896_, 5);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; lean_object* v_unused_3944_; lean_object* v_unused_3945_; 
v_unused_3943_ = lean_ctor_get(v___x_3896_, 4);
lean_dec(v_unused_3943_);
v_unused_3944_ = lean_ctor_get(v___x_3896_, 1);
lean_dec(v_unused_3944_);
v_unused_3945_ = lean_ctor_get(v___x_3896_, 0);
lean_dec(v_unused_3945_);
v___x_3902_ = v___x_3896_;
v_isShared_3903_ = v_isSharedCheck_3942_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_monotonicity_x3f_3900_);
lean_inc(v_modifiers_3897_);
lean_inc(v_ref_3898_);
lean_dec(v___x_3896_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3942_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_stx_3904_; uint8_t v_visibility_3905_; uint8_t v_isProtected_3906_; uint8_t v_computeKind_3907_; uint8_t v_recKind_3908_; uint8_t v_isUnsafe_3909_; lean_object* v_attrs_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3940_; 
v_stx_3904_ = lean_ctor_get(v_modifiers_3897_, 0);
v_visibility_3905_ = lean_ctor_get_uint8(v_modifiers_3897_, sizeof(void*)*3);
v_isProtected_3906_ = lean_ctor_get_uint8(v_modifiers_3897_, sizeof(void*)*3 + 1);
v_computeKind_3907_ = lean_ctor_get_uint8(v_modifiers_3897_, sizeof(void*)*3 + 2);
v_recKind_3908_ = lean_ctor_get_uint8(v_modifiers_3897_, sizeof(void*)*3 + 3);
v_isUnsafe_3909_ = lean_ctor_get_uint8(v_modifiers_3897_, sizeof(void*)*3 + 4);
v_attrs_3910_ = lean_ctor_get(v_modifiers_3897_, 2);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_modifiers_3897_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; 
v_unused_3941_ = lean_ctor_get(v_modifiers_3897_, 1);
lean_dec(v_unused_3941_);
v___x_3912_ = v_modifiers_3897_;
v_isShared_3913_ = v_isSharedCheck_3940_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_attrs_3910_);
lean_inc(v_stx_3904_);
lean_dec(v_modifiers_3897_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3940_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v_fst_3916_; lean_object* v_snd_3917_; lean_object* v___x_3918_; lean_object* v___f_3919_; lean_object* v___x_3920_; lean_object* v___x_3922_; 
v___x_3914_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3915_ = lean_array_get_borrowed(v___x_3914_, v_a_3885_, v___x_3895_);
lean_dec(v___x_3895_);
v_fst_3916_ = lean_ctor_get(v___x_3915_, 0);
v_snd_3917_ = lean_ctor_get(v___x_3915_, 1);
v___x_3918_ = lean_box(v___x_3890_);
lean_inc_ref(v___x_3884_);
v___f_3919_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3919_, 0, v___x_3884_);
lean_closure_set(v___f_3919_, 1, v___x_3918_);
v___x_3920_ = lean_box(0);
if (v_isShared_3913_ == 0)
{
lean_ctor_set(v___x_3912_, 1, v___x_3920_);
v___x_3922_ = v___x_3912_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_stx_3904_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_attrs_3910_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3, v_visibility_3905_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 1, v_isProtected_3906_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 2, v_computeKind_3907_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 3, v_recKind_3908_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 4, v_isUnsafe_3909_);
v___x_3922_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; uint8_t v___x_3924_; uint8_t v___y_3926_; 
v___x_3923_ = l_Lean_Elab_Modifiers_filterAttrs(v___x_3922_, v___f_3919_);
v___x_3924_ = 0;
if (v_isGreatest_3899_ == 0)
{
uint8_t v___x_3937_; 
v___x_3937_ = 2;
v___y_3926_ = v___x_3937_;
goto v___jp_3925_;
}
else
{
uint8_t v___x_3938_; 
v___x_3938_ = 1;
v___y_3926_ = v___x_3938_;
goto v___jp_3925_;
}
v___jp_3925_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
lean_inc_n(v_ref_3898_, 2);
v___x_3927_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3927_, 0, v_ref_3898_);
lean_ctor_set(v___x_3927_, 1, v_monotonicity_x3f_3900_);
lean_ctor_set_uint8(v___x_3927_, sizeof(void*)*2, v___y_3926_);
v___x_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 5, v___x_3893_);
lean_ctor_set(v___x_3902_, 4, v___x_3920_);
lean_ctor_set(v___x_3902_, 3, v___x_3928_);
lean_ctor_set(v___x_3902_, 2, v___x_3920_);
lean_ctor_set(v___x_3902_, 1, v___x_3920_);
lean_ctor_set(v___x_3902_, 0, v_ref_3898_);
v___x_3930_ = v___x_3902_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_ref_3898_);
lean_ctor_set(v_reuseFailAlloc_3936_, 1, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3936_, 2, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3936_, 3, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3936_, 4, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3936_, 5, v___x_3893_);
v___x_3930_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; size_t v___x_3932_; size_t v___x_3933_; lean_object* v___x_3934_; 
lean_ctor_set_uint8(v___x_3930_, sizeof(void*)*6, v___x_3890_);
lean_inc(v_snd_3917_);
lean_inc(v_fst_3916_);
lean_inc(v___x_3886_);
lean_inc(v_ref_3898_);
v___x_3931_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3931_, 0, v_ref_3898_);
lean_ctor_set(v___x_3931_, 1, v___x_3886_);
lean_ctor_set(v___x_3931_, 2, v___x_3923_);
lean_ctor_set(v___x_3931_, 3, v_fst_3916_);
lean_ctor_set(v___x_3931_, 4, v_ref_3898_);
lean_ctor_set(v___x_3931_, 5, v___x_3893_);
lean_ctor_set(v___x_3931_, 6, v_snd_3917_);
lean_ctor_set(v___x_3931_, 7, v_v_3892_);
lean_ctor_set(v___x_3931_, 8, v___x_3930_);
lean_ctor_set_uint8(v___x_3931_, sizeof(void*)*9, v___x_3924_);
v___x_3932_ = ((size_t)1ULL);
v___x_3933_ = lean_usize_add(v_i_3888_, v___x_3932_);
v___x_3934_ = lean_array_uset(v_bs_x27_3894_, v_i_3888_, v___x_3931_);
v_i_3888_ = v___x_3933_;
v_bs_3889_ = v___x_3934_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object* v_coinductiveElabData_3946_, lean_object* v___x_3947_, lean_object* v_a_3948_, lean_object* v___x_3949_, lean_object* v_sz_3950_, lean_object* v_i_3951_, lean_object* v_bs_3952_){
_start:
{
size_t v_sz_boxed_3953_; size_t v_i_boxed_3954_; lean_object* v_res_3955_; 
v_sz_boxed_3953_ = lean_unbox_usize(v_sz_3950_);
lean_dec(v_sz_3950_);
v_i_boxed_3954_ = lean_unbox_usize(v_i_3951_);
lean_dec(v_i_3951_);
v_res_3955_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_3946_, v___x_3947_, v_a_3948_, v___x_3949_, v_sz_boxed_3953_, v_i_boxed_3954_, v_bs_3952_);
lean_dec_ref(v_a_3948_);
lean_dec_ref(v_coinductiveElabData_3946_);
return v_res_3955_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0));
v___x_3958_ = l_Lean_stringToMessageData(v___x_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object* v_constName_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_){
_start:
{
lean_object* v___x_3967_; lean_object* v_env_3968_; lean_object* v___x_3969_; 
v___x_3967_ = lean_st_ref_get(v___y_3965_);
v_env_3968_ = lean_ctor_get(v___x_3967_, 0);
lean_inc_ref(v_env_3968_);
lean_dec(v___x_3967_);
lean_inc(v_constName_3959_);
v___x_3969_ = l_Lean_isInductiveCore_x3f(v_env_3968_, v_constName_3959_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v___x_3970_; uint8_t v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3970_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_3971_ = 0;
v___x_3972_ = l_Lean_MessageData_ofConstName(v_constName_3959_, v___x_3971_);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3970_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
v___x_3975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3973_);
lean_ctor_set(v___x_3975_, 1, v___x_3974_);
v___x_3976_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_3975_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
return v___x_3976_;
}
else
{
lean_object* v_val_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec(v_constName_3959_);
v_val_3977_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3969_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_val_3977_);
lean_dec(v___x_3969_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
lean_ctor_set_tag(v___x_3979_, 0);
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_val_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object* v_constName_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
lean_object* v_res_3993_; 
v_res_3993_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t v_sz_3994_, size_t v_i_3995_, lean_object* v_bs_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
uint8_t v___x_4004_; 
v___x_4004_ = lean_usize_dec_lt(v_i_3995_, v_sz_3994_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4005_; 
v___x_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4005_, 0, v_bs_3996_);
return v___x_4005_;
}
else
{
lean_object* v_v_4006_; lean_object* v_declName_4007_; lean_object* v___x_4008_; lean_object* v_bs_x27_4009_; lean_object* v___x_4010_; 
v_v_4006_ = lean_array_uget_borrowed(v_bs_3996_, v_i_3995_);
v_declName_4007_ = lean_ctor_get(v_v_4006_, 1);
lean_inc(v_declName_4007_);
v___x_4008_ = lean_unsigned_to_nat(0u);
v_bs_x27_4009_ = lean_array_uset(v_bs_3996_, v_i_3995_, v___x_4008_);
v___x_4010_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_4007_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; size_t v___x_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = ((size_t)1ULL);
v___x_4013_ = lean_usize_add(v_i_3995_, v___x_4012_);
v___x_4014_ = lean_array_uset(v_bs_x27_4009_, v_i_3995_, v_a_4011_);
v_i_3995_ = v___x_4013_;
v_bs_3996_ = v___x_4014_;
goto _start;
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v_bs_x27_4009_);
v_a_4016_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4010_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4010_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object* v_sz_4024_, lean_object* v_i_4025_, lean_object* v_bs_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
size_t v_sz_boxed_4034_; size_t v_i_boxed_4035_; lean_object* v_res_4036_; 
v_sz_boxed_4034_ = lean_unbox_usize(v_sz_4024_);
lean_dec(v_sz_4024_);
v_i_boxed_4035_ = lean_unbox_usize(v_i_4025_);
lean_dec(v_i_4025_);
v_res_4036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_4034_, v_i_boxed_4035_, v_bs_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
if (lean_obj_tag(v_a_4037_) == 0)
{
lean_object* v___x_4039_; 
v___x_4039_ = l_List_reverse___redArg(v_a_4038_);
return v___x_4039_;
}
else
{
lean_object* v_head_4040_; lean_object* v_tail_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4050_; 
v_head_4040_ = lean_ctor_get(v_a_4037_, 0);
v_tail_4041_ = lean_ctor_get(v_a_4037_, 1);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_a_4037_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4043_ = v_a_4037_;
v_isShared_4044_ = v_isSharedCheck_4050_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_tail_4041_);
lean_inc(v_head_4040_);
lean_dec(v_a_4037_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4050_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v___x_4047_; 
v___x_4045_ = l_Lean_MessageData_ofName(v_head_4040_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 1, v_a_4038_);
lean_ctor_set(v___x_4043_, 0, v___x_4045_);
v___x_4047_ = v___x_4043_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v___x_4045_);
lean_ctor_set(v_reuseFailAlloc_4049_, 1, v_a_4038_);
v___x_4047_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
v_a_4037_ = v_tail_4041_;
v_a_4038_ = v___x_4047_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t v_sz_4051_, size_t v_i_4052_, lean_object* v_bs_4053_){
_start:
{
uint8_t v___x_4054_; 
v___x_4054_ = lean_usize_dec_lt(v_i_4052_, v_sz_4051_);
if (v___x_4054_ == 0)
{
return v_bs_4053_;
}
else
{
lean_object* v_v_4055_; lean_object* v_declName_4056_; lean_object* v___x_4057_; lean_object* v_bs_x27_4058_; size_t v___x_4059_; size_t v___x_4060_; lean_object* v___x_4061_; 
v_v_4055_ = lean_array_uget_borrowed(v_bs_4053_, v_i_4052_);
v_declName_4056_ = lean_ctor_get(v_v_4055_, 1);
lean_inc(v_declName_4056_);
v___x_4057_ = lean_unsigned_to_nat(0u);
v_bs_x27_4058_ = lean_array_uset(v_bs_4053_, v_i_4052_, v___x_4057_);
v___x_4059_ = ((size_t)1ULL);
v___x_4060_ = lean_usize_add(v_i_4052_, v___x_4059_);
v___x_4061_ = lean_array_uset(v_bs_x27_4058_, v_i_4052_, v_declName_4056_);
v_i_4052_ = v___x_4060_;
v_bs_4053_ = v___x_4061_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object* v_sz_4063_, lean_object* v_i_4064_, lean_object* v_bs_4065_){
_start:
{
size_t v_sz_boxed_4066_; size_t v_i_boxed_4067_; lean_object* v_res_4068_; 
v_sz_boxed_4066_ = lean_unbox_usize(v_sz_4063_);
lean_dec(v_sz_4063_);
v_i_boxed_4067_ = lean_unbox_usize(v_i_4064_);
lean_dec(v_i_4064_);
v_res_4068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_4066_, v_i_boxed_4067_, v_bs_4065_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v___x_4069_, lean_object* v___x_4070_, lean_object* v_numParams_4071_, uint8_t v___x_4072_, lean_object* v_args_4073_, lean_object* v_body_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; uint8_t v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; 
lean_inc_ref(v_args_4073_);
v___x_4082_ = l_Array_toSubarray___redArg(v_args_4073_, v___x_4069_, v___x_4070_);
v___x_4083_ = l_Subarray_copy___redArg(v___x_4082_);
v___x_4084_ = lean_array_get_size(v_args_4073_);
v___x_4085_ = l_Array_toSubarray___redArg(v_args_4073_, v_numParams_4071_, v___x_4084_);
v___x_4086_ = l_Subarray_copy___redArg(v___x_4085_);
v___x_4087_ = l_Array_append___redArg(v___x_4083_, v___x_4086_);
lean_dec_ref(v___x_4086_);
v___x_4088_ = 0;
v___x_4089_ = 1;
v___x_4090_ = l_Lean_Meta_mkForallFVars(v___x_4087_, v_body_4074_, v___x_4088_, v___x_4072_, v___x_4072_, v___x_4089_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec_ref(v___x_4087_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v___x_4091_, lean_object* v___x_4092_, lean_object* v_numParams_4093_, lean_object* v___x_4094_, lean_object* v_args_4095_, lean_object* v_body_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
uint8_t v___x_6091__boxed_4104_; lean_object* v_res_4105_; 
v___x_6091__boxed_4104_ = lean_unbox(v___x_4094_);
v_res_4105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v___x_4091_, v___x_4092_, v_numParams_4093_, v___x_6091__boxed_4104_, v_args_4095_, v_body_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_4106_, size_t v_sz_4107_, size_t v_i_4108_, lean_object* v_bs_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
uint8_t v___x_4117_; 
v___x_4117_ = lean_usize_dec_lt(v_i_4108_, v_sz_4107_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; 
lean_dec(v___x_4106_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v_bs_4109_);
return v___x_4118_;
}
else
{
lean_object* v_v_4119_; lean_object* v_toConstantVal_4120_; lean_object* v_numParams_4121_; lean_object* v_name_4122_; lean_object* v_type_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___f_4126_; lean_object* v_bs_x27_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; 
v_v_4119_ = lean_array_uget_borrowed(v_bs_4109_, v_i_4108_);
v_toConstantVal_4120_ = lean_ctor_get(v_v_4119_, 0);
v_numParams_4121_ = lean_ctor_get(v_v_4119_, 1);
v_name_4122_ = lean_ctor_get(v_toConstantVal_4120_, 0);
lean_inc(v_name_4122_);
v_type_4123_ = lean_ctor_get(v_toConstantVal_4120_, 2);
lean_inc_ref(v_type_4123_);
v___x_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = lean_box(v___x_4117_);
lean_inc(v_numParams_4121_);
lean_inc(v___x_4106_);
v___f_4126_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4126_, 0, v___x_4124_);
lean_closure_set(v___f_4126_, 1, v___x_4106_);
lean_closure_set(v___f_4126_, 2, v_numParams_4121_);
lean_closure_set(v___f_4126_, 3, v___x_4125_);
v_bs_x27_4127_ = lean_array_uset(v_bs_4109_, v_i_4108_, v___x_4124_);
v___x_4128_ = 0;
v___x_4129_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4123_, v___f_4126_, v___x_4128_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; size_t v___x_4133_; size_t v___x_4134_; lean_object* v___x_4135_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref_known(v___x_4129_, 1);
v___x_4131_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4122_);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
lean_ctor_set(v___x_4132_, 1, v_a_4130_);
v___x_4133_ = ((size_t)1ULL);
v___x_4134_ = lean_usize_add(v_i_4108_, v___x_4133_);
v___x_4135_ = lean_array_uset(v_bs_x27_4127_, v_i_4108_, v___x_4132_);
v_i_4108_ = v___x_4134_;
v_bs_4109_ = v___x_4135_;
goto _start;
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v_bs_x27_4127_);
lean_dec(v_name_4122_);
lean_dec(v___x_4106_);
v_a_4137_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4129_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4129_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object* v___x_4145_, lean_object* v_sz_4146_, lean_object* v_i_4147_, lean_object* v_bs_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
size_t v_sz_boxed_4156_; size_t v_i_boxed_4157_; lean_object* v_res_4158_; 
v_sz_boxed_4156_ = lean_unbox_usize(v_sz_4146_);
lean_dec(v_sz_4146_);
v_i_boxed_4157_ = lean_unbox_usize(v_i_4147_);
lean_dec(v_i_4147_);
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4145_, v_sz_boxed_4156_, v_i_boxed_4157_, v_bs_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object* v___x_4159_, size_t v_sz_4160_, size_t v_i_4161_, lean_object* v_bs_4162_){
_start:
{
uint8_t v___x_4163_; 
v___x_4163_ = lean_usize_dec_lt(v_i_4161_, v_sz_4160_);
if (v___x_4163_ == 0)
{
lean_dec(v___x_4159_);
return v_bs_4162_;
}
else
{
lean_object* v_v_4164_; lean_object* v_fst_4165_; lean_object* v___x_4166_; lean_object* v_bs_x27_4167_; lean_object* v___x_4168_; size_t v___x_4169_; size_t v___x_4170_; lean_object* v___x_4171_; 
v_v_4164_ = lean_array_uget_borrowed(v_bs_4162_, v_i_4161_);
v_fst_4165_ = lean_ctor_get(v_v_4164_, 0);
lean_inc(v_fst_4165_);
v___x_4166_ = lean_unsigned_to_nat(0u);
v_bs_x27_4167_ = lean_array_uset(v_bs_4162_, v_i_4161_, v___x_4166_);
lean_inc(v___x_4159_);
v___x_4168_ = l_Lean_mkConst(v_fst_4165_, v___x_4159_);
v___x_4169_ = ((size_t)1ULL);
v___x_4170_ = lean_usize_add(v_i_4161_, v___x_4169_);
v___x_4171_ = lean_array_uset(v_bs_x27_4167_, v_i_4161_, v___x_4168_);
v_i_4161_ = v___x_4170_;
v_bs_4162_ = v___x_4171_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object* v___x_4173_, lean_object* v_sz_4174_, lean_object* v_i_4175_, lean_object* v_bs_4176_){
_start:
{
size_t v_sz_boxed_4177_; size_t v_i_boxed_4178_; lean_object* v_res_4179_; 
v_sz_boxed_4177_ = lean_unbox_usize(v_sz_4174_);
lean_dec(v_sz_4174_);
v_i_boxed_4178_ = lean_unbox_usize(v_i_4175_);
lean_dec(v_i_4175_);
v_res_4179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4173_, v_sz_boxed_4177_, v_i_boxed_4178_, v_bs_4176_);
return v_res_4179_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCoinductive___closed__1(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = ((lean_object*)(l_Lean_Elab_Command_elabCoinductive___closed__0));
v___x_4182_ = l_Lean_stringToMessageData(v___x_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object* v_coinductiveElabData_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_toCold_4191_; lean_object* v_options_4192_; lean_object* v_inheritedTraceOptions_4193_; uint8_t v_hasTrace_4194_; lean_object* v___x_4195_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; 
v_toCold_4191_ = lean_ctor_get(v_a_4188_, 0);
v_options_4192_ = lean_ctor_get(v_toCold_4191_, 2);
v_inheritedTraceOptions_4193_ = lean_ctor_get(v_toCold_4191_, 11);
v_hasTrace_4194_ = lean_ctor_get_uint8(v_options_4192_, sizeof(void*)*1);
v___x_4195_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4194_ == 0)
{
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
v___y_4199_ = v_a_4186_;
v___y_4200_ = v_a_4187_;
v___y_4201_ = v_a_4188_;
v___y_4202_ = v_a_4189_;
goto v___jp_4196_;
}
else
{
lean_object* v_cls_4264_; lean_object* v___x_4265_; uint8_t v___x_4266_; 
v_cls_4264_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4265_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4193_, v_options_4192_, v___x_4265_);
if (v___x_4266_ == 0)
{
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
v___y_4199_ = v_a_4186_;
v___y_4200_ = v_a_4187_;
v___y_4201_ = v_a_4188_;
v___y_4202_ = v_a_4189_;
goto v___jp_4196_;
}
else
{
lean_object* v___x_4267_; size_t v_sz_4268_; size_t v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4267_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4268_ = lean_array_size(v_coinductiveElabData_4183_);
v___x_4269_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4183_);
v___x_4270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4268_, v___x_4269_, v_coinductiveElabData_4183_);
v___x_4271_ = lean_array_to_list(v___x_4270_);
v___x_4272_ = lean_box(0);
v___x_4273_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4271_, v___x_4272_);
v___x_4274_ = l_Lean_MessageData_ofList(v___x_4273_);
v___x_4275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4267_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4264_, v___x_4275_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_dec_ref_known(v___x_4276_, 1);
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
v___y_4199_ = v_a_4186_;
v___y_4200_ = v_a_4187_;
v___y_4201_ = v_a_4188_;
v___y_4202_ = v_a_4189_;
goto v___jp_4196_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4183_);
return v___x_4276_;
}
}
}
v___jp_4196_:
{
size_t v_sz_4203_; size_t v___x_4204_; lean_object* v___x_4205_; 
v_sz_4203_ = lean_array_size(v_coinductiveElabData_4183_);
v___x_4204_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4183_);
v___x_4205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4203_, v___x_4204_, v_coinductiveElabData_4183_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v_toConstantVal_4209_; lean_object* v_numParams_4210_; lean_object* v_levelParams_4211_; lean_object* v_type_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; size_t v_sz_4217_; lean_object* v___x_4218_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc_n(v_a_4206_, 2);
lean_dec_ref_known(v___x_4205_, 1);
v___x_4207_ = lean_unsigned_to_nat(0u);
v___x_4208_ = lean_array_get_borrowed(v___x_4195_, v_a_4206_, v___x_4207_);
v_toConstantVal_4209_ = lean_ctor_get(v___x_4208_, 0);
v_numParams_4210_ = lean_ctor_get(v___x_4208_, 1);
v_levelParams_4211_ = lean_ctor_get(v_toConstantVal_4209_, 1);
v_type_4212_ = lean_ctor_get(v_toConstantVal_4209_, 2);
v___x_4213_ = lean_box(0);
lean_inc(v_levelParams_4211_);
v___x_4214_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4211_, v___x_4213_);
v___x_4215_ = lean_array_get_size(v_a_4206_);
v___x_4216_ = lean_nat_sub(v_numParams_4210_, v___x_4215_);
v_sz_4217_ = lean_array_size(v_a_4206_);
lean_inc(v___x_4216_);
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4216_, v_sz_4217_, v___x_4204_, v_a_4206_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; size_t v_sz_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___f_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; lean_object* v___x_4227_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc_n(v_a_4219_, 2);
lean_dec_ref_known(v___x_4218_, 1);
v_sz_4220_ = lean_array_size(v_a_4219_);
lean_inc(v___x_4214_);
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4214_, v_sz_4220_, v___x_4204_, v_a_4219_);
v___x_4222_ = lean_box_usize(v_sz_4217_);
v___x_4223_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4206_);
v___f_4224_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4224_, 0, v___x_4214_);
lean_closure_set(v___f_4224_, 1, v___x_4221_);
lean_closure_set(v___f_4224_, 2, v___x_4222_);
lean_closure_set(v___f_4224_, 3, v___x_4223_);
lean_closure_set(v___f_4224_, 4, v_a_4206_);
lean_inc(v___x_4216_);
v___x_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4216_);
v___x_4226_ = 0;
lean_inc_ref(v_type_4212_);
v___x_4227_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4212_, v___x_4225_, v___f_4224_, v___x_4226_, v___x_4226_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4229_; lean_object* v_env_4230_; size_t v_sz_4231_; lean_object* v_lctx_4232_; lean_object* v_localInstances_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___x_4229_ = lean_st_ref_get(v___y_4202_);
v_env_4230_ = lean_ctor_get(v___x_4229_, 0);
lean_inc_ref(v_env_4230_);
lean_dec(v___x_4229_);
v_sz_4231_ = lean_array_size(v_a_4228_);
v_lctx_4232_ = lean_ctor_get(v___y_4199_, 2);
v_localInstances_4233_ = lean_ctor_get(v___y_4199_, 3);
lean_inc(v_levelParams_4211_);
v___x_4234_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4183_, v_env_4230_, v_a_4219_, v_levelParams_4211_, v_sz_4231_, v___x_4204_, v_a_4228_);
lean_dec(v_a_4219_);
lean_inc_ref(v_localInstances_4233_);
lean_inc_ref(v_lctx_4232_);
v___x_4235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4235_, 0, v_lctx_4232_);
lean_ctor_set(v___x_4235_, 1, v_localInstances_4233_);
v___x_4236_ = l_Lean_Elab_partialFixpoint(v___x_4235_, v___x_4234_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v___x_4237_; 
lean_dec_ref_known(v___x_4236_, 1);
lean_inc(v_a_4206_);
v___x_4237_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4206_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v___x_4238_; 
lean_dec_ref_known(v___x_4237_, 1);
lean_inc(v_a_4206_);
v___x_4238_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4216_, v_a_4206_, v_coinductiveElabData_4183_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v___x_4239_; 
lean_dec_ref_known(v___x_4238_, 1);
v___x_4239_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4206_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
return v___x_4239_;
}
else
{
lean_dec(v_a_4206_);
return v___x_4238_;
}
}
else
{
lean_dec(v___x_4216_);
lean_dec(v_a_4206_);
lean_dec_ref(v_coinductiveElabData_4183_);
return v___x_4237_;
}
}
else
{
lean_dec(v___x_4216_);
lean_dec(v_a_4206_);
lean_dec_ref(v_coinductiveElabData_4183_);
return v___x_4236_;
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec(v_a_4219_);
lean_dec(v___x_4216_);
lean_dec(v_a_4206_);
lean_dec_ref(v_coinductiveElabData_4183_);
v_a_4240_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4227_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4227_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
lean_object* v_a_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
lean_dec(v___x_4216_);
lean_dec(v___x_4214_);
lean_dec(v_a_4206_);
lean_dec_ref(v_coinductiveElabData_4183_);
v_a_4248_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4250_ = v___x_4218_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_a_4248_);
lean_dec(v___x_4218_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec_ref(v_coinductiveElabData_4183_);
v_a_4256_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4205_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4205_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
lean_dec(v_a_4283_);
lean_dec_ref(v_a_4282_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v_params_4288_, size_t v_sz_4289_, size_t v_i_4290_, lean_object* v_bs_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4286_, v___x_4287_, v_params_4288_, v_sz_4289_, v_i_4290_, v_bs_4291_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v_params_4302_, lean_object* v_sz_4303_, lean_object* v_i_4304_, lean_object* v_bs_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
size_t v_sz_boxed_4313_; size_t v_i_boxed_4314_; lean_object* v_res_4315_; 
v_sz_boxed_4313_ = lean_unbox_usize(v_sz_4303_);
lean_dec(v_sz_4303_);
v_i_boxed_4314_ = lean_unbox_usize(v_i_4304_);
lean_dec(v_i_4304_);
v_res_4315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4300_, v___x_4301_, v_params_4302_, v_sz_boxed_4313_, v_i_boxed_4314_, v_bs_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4316_, lean_object* v___x_4317_, lean_object* v_a_4318_, lean_object* v___x_4319_, lean_object* v_as_4320_, size_t v_sz_4321_, size_t v_i_4322_, lean_object* v_bs_4323_){
_start:
{
lean_object* v___x_4324_; 
v___x_4324_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4316_, v___x_4317_, v_a_4318_, v___x_4319_, v_sz_4321_, v_i_4322_, v_bs_4323_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4325_, lean_object* v___x_4326_, lean_object* v_a_4327_, lean_object* v___x_4328_, lean_object* v_as_4329_, lean_object* v_sz_4330_, lean_object* v_i_4331_, lean_object* v_bs_4332_){
_start:
{
size_t v_sz_boxed_4333_; size_t v_i_boxed_4334_; lean_object* v_res_4335_; 
v_sz_boxed_4333_ = lean_unbox_usize(v_sz_4330_);
lean_dec(v_sz_4330_);
v_i_boxed_4334_ = lean_unbox_usize(v_i_4331_);
lean_dec(v_i_4331_);
v_res_4335_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4325_, v___x_4326_, v_a_4327_, v___x_4328_, v_as_4329_, v_sz_boxed_4333_, v_i_boxed_4334_, v_bs_4332_);
lean_dec_ref(v_as_4329_);
lean_dec_ref(v_a_4327_);
lean_dec_ref(v_coinductiveElabData_4325_);
return v_res_4335_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_UnusedVariables(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Coinductive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_UnusedVariables(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default = _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default);
l_Lean_Elab_Command_instInhabitedCoinductiveElabData = _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData();
lean_mark_persistent(l_Lean_Elab_Command_instInhabitedCoinductiveElabData);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Coinductive(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Lean_Linter_UnusedVariables(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Coinductive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_PartialFixpoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_UnusedVariables(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Coinductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Coinductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Coinductive(builtin);
}
#ifdef __cplusplus
}
#endif
