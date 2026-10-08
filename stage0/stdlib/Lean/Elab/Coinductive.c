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
lean_object* v___x_303_; uint8_t v___y_305_; uint8_t v___y_312_; lean_object* v_env_315_; uint8_t v___x_316_; 
v___x_303_ = lean_st_ref_get(v___y_301_);
v_env_315_ = lean_ctor_get(v___x_303_, 0);
lean_inc_ref_n(v_env_315_, 2);
lean_dec(v___x_303_);
v___x_316_ = l_Lean_Environment_hasUnsafe(v_env_315_, v_type_298_);
if (v___x_316_ == 0)
{
uint8_t v___x_317_; 
v___x_317_ = l_Lean_Environment_hasUnsafe(v_env_315_, v_value_299_);
v___y_312_ = v___x_317_;
goto v___jp_311_;
}
else
{
lean_dec_ref(v_env_315_);
v___y_312_ = v___x_316_;
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
if (v___y_312_ == 0)
{
uint8_t v___x_313_; 
v___x_313_ = 1;
v___y_305_ = v___x_313_;
goto v___jp_304_;
}
else
{
uint8_t v___x_314_; 
v___x_314_ = 0;
v___y_305_ = v___x_314_;
goto v___jp_304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg___boxed(lean_object* v_name_318_, lean_object* v_levelParams_319_, lean_object* v_type_320_, lean_object* v_value_321_, lean_object* v_hints_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_318_, v_levelParams_319_, v_type_320_, v_value_321_, v_hints_322_, v___y_323_);
lean_dec(v___y_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(lean_object* v_name_326_, lean_object* v_levelParams_327_, lean_object* v_type_328_, lean_object* v_value_329_, lean_object* v_hints_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_326_, v_levelParams_327_, v_type_328_, v_value_329_, v_hints_330_, v___y_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___boxed(lean_object* v_name_337_, lean_object* v_levelParams_338_, lean_object* v_type_339_, lean_object* v_value_340_, lean_object* v_hints_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(v_name_337_, v_levelParams_338_, v_type_339_, v_value_340_, v_hints_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
if (lean_obj_tag(v_a_348_) == 0)
{
lean_object* v___x_350_; 
v___x_350_ = l_List_reverse___redArg(v_a_349_);
return v___x_350_;
}
else
{
lean_object* v_head_351_; lean_object* v_tail_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_361_; 
v_head_351_ = lean_ctor_get(v_a_348_, 0);
v_tail_352_ = lean_ctor_get(v_a_348_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v_a_348_);
if (v_isSharedCheck_361_ == 0)
{
v___x_354_ = v_a_348_;
v_isShared_355_ = v_isSharedCheck_361_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_tail_352_);
lean_inc(v_head_351_);
lean_dec(v_a_348_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_361_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = l_Lean_mkLevelParam(v_head_351_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_a_349_);
lean_ctor_set(v___x_354_, 0, v___x_356_);
v___x_358_ = v___x_354_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_a_349_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
v_a_348_ = v_tail_352_;
v_a_349_ = v___x_358_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(lean_object* v_x_362_, lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_ks_366_; lean_object* v_vs_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_391_; 
v_ks_366_ = lean_ctor_get(v_x_362_, 0);
v_vs_367_ = lean_ctor_get(v_x_362_, 1);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_391_ == 0)
{
v___x_369_ = v_x_362_;
v_isShared_370_ = v_isSharedCheck_391_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_vs_367_);
lean_inc(v_ks_366_);
lean_dec(v_x_362_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_391_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = lean_array_get_size(v_ks_366_);
v___x_372_ = lean_nat_dec_lt(v_x_363_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
lean_dec(v_x_363_);
v___x_373_ = lean_array_push(v_ks_366_, v_x_364_);
v___x_374_ = lean_array_push(v_vs_367_, v_x_365_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_374_);
lean_ctor_set(v___x_369_, 0, v___x_373_);
v___x_376_ = v___x_369_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v_k_x27_378_; uint8_t v___x_379_; 
v_k_x27_378_ = lean_array_fget_borrowed(v_ks_366_, v_x_363_);
v___x_379_ = l_Lean_instBEqMVarId_beq(v_x_364_, v_k_x27_378_);
if (v___x_379_ == 0)
{
lean_object* v___x_381_; 
if (v_isShared_370_ == 0)
{
v___x_381_ = v___x_369_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_ks_366_);
lean_ctor_set(v_reuseFailAlloc_385_, 1, v_vs_367_);
v___x_381_ = v_reuseFailAlloc_385_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_nat_add(v_x_363_, v___x_382_);
lean_dec(v_x_363_);
v_x_362_ = v___x_381_;
v_x_363_ = v___x_383_;
goto _start;
}
}
else
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_389_; 
v___x_386_ = lean_array_fset(v_ks_366_, v_x_363_, v_x_364_);
v___x_387_ = lean_array_fset(v_vs_367_, v_x_363_, v_x_365_);
lean_dec(v_x_363_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_387_);
lean_ctor_set(v___x_369_, 0, v___x_386_);
v___x_389_ = v___x_369_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v___x_386_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_387_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(lean_object* v_n_392_, lean_object* v_k_393_, lean_object* v_v_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_n_392_, v___x_395_, v_k_393_, v_v_394_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(lean_object* v_x_398_, size_t v_x_399_, size_t v_x_400_, lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_es_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v_j_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_es_403_ = lean_ctor_get(v_x_398_, 0);
v___x_404_ = ((size_t)31ULL);
v___x_405_ = lean_usize_land(v_x_399_, v___x_404_);
v_j_406_ = lean_usize_to_nat(v___x_405_);
v___x_407_ = lean_array_get_size(v_es_403_);
v___x_408_ = lean_nat_dec_lt(v_j_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_dec(v_j_406_);
lean_dec(v_x_402_);
lean_dec(v_x_401_);
return v_x_398_;
}
else
{
lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_447_; 
lean_inc_ref(v_es_403_);
v_isSharedCheck_447_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_x_398_, 0);
lean_dec(v_unused_448_);
v___x_410_ = v_x_398_;
v_isShared_411_ = v_isSharedCheck_447_;
goto v_resetjp_409_;
}
else
{
lean_dec(v_x_398_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_447_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_v_412_; lean_object* v___x_413_; lean_object* v_xs_x27_414_; lean_object* v___y_416_; 
v_v_412_ = lean_array_fget(v_es_403_, v_j_406_);
v___x_413_ = lean_box(0);
v_xs_x27_414_ = lean_array_fset(v_es_403_, v_j_406_, v___x_413_);
switch(lean_obj_tag(v_v_412_))
{
case 0:
{
lean_object* v_key_421_; lean_object* v_val_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_key_421_ = lean_ctor_get(v_v_412_, 0);
v_val_422_ = lean_ctor_get(v_v_412_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_432_ == 0)
{
v___x_424_ = v_v_412_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_val_422_);
lean_inc(v_key_421_);
lean_dec(v_v_412_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
uint8_t v___x_426_; 
v___x_426_ = l_Lean_instBEqMVarId_beq(v_x_401_, v_key_421_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_del_object(v___x_424_);
v___x_427_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_421_, v_val_422_, v_x_401_, v_x_402_);
v___x_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
v___y_416_ = v___x_428_;
goto v___jp_415_;
}
else
{
lean_object* v___x_430_; 
lean_dec(v_val_422_);
lean_dec(v_key_421_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v_x_402_);
lean_ctor_set(v___x_424_, 0, v_x_401_);
v___x_430_ = v___x_424_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_x_401_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_x_402_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
v___y_416_ = v___x_430_;
goto v___jp_415_;
}
}
}
}
case 1:
{
lean_object* v_node_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_445_; 
v_node_433_ = lean_ctor_get(v_v_412_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v_v_412_);
if (v_isSharedCheck_445_ == 0)
{
v___x_435_ = v_v_412_;
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_node_433_);
lean_dec(v_v_412_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
size_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_437_ = ((size_t)5ULL);
v___x_438_ = lean_usize_shift_right(v_x_399_, v___x_437_);
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_x_400_, v___x_439_);
v___x_441_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_node_433_, v___x_438_, v___x_440_, v_x_401_, v_x_402_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_441_);
v___x_443_ = v___x_435_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
v___y_416_ = v___x_443_;
goto v___jp_415_;
}
}
}
default: 
{
lean_object* v___x_446_; 
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_x_401_);
lean_ctor_set(v___x_446_, 1, v_x_402_);
v___y_416_ = v___x_446_;
goto v___jp_415_;
}
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_array_fset(v_xs_x27_414_, v_j_406_, v___y_416_);
lean_dec(v_j_406_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_417_);
v___x_419_ = v___x_410_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
else
{
lean_object* v_ks_449_; lean_object* v_vs_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_468_; 
v_ks_449_ = lean_ctor_get(v_x_398_, 0);
v_vs_450_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_468_ == 0)
{
v___x_452_ = v_x_398_;
v_isShared_453_ = v_isSharedCheck_468_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_vs_450_);
lean_inc(v_ks_449_);
lean_dec(v_x_398_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_468_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_ks_449_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v_vs_450_);
v___x_455_ = v_reuseFailAlloc_467_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v_newNode_456_; size_t v___x_457_; uint8_t v___x_458_; 
v_newNode_456_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v___x_455_, v_x_401_, v_x_402_);
v___x_457_ = ((size_t)7ULL);
v___x_458_ = lean_usize_dec_le(v___x_457_, v_x_400_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_459_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_456_);
v___x_460_ = lean_unsigned_to_nat(4u);
v___x_461_ = lean_nat_dec_lt(v___x_459_, v___x_460_);
lean_dec(v___x_459_);
if (v___x_461_ == 0)
{
lean_object* v_ks_462_; lean_object* v_vs_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v_ks_462_ = lean_ctor_get(v_newNode_456_, 0);
lean_inc_ref(v_ks_462_);
v_vs_463_ = lean_ctor_get(v_newNode_456_, 1);
lean_inc_ref(v_vs_463_);
lean_dec_ref(v_newNode_456_);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0);
v___x_466_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_x_400_, v_ks_462_, v_vs_463_, v___x_464_, v___x_465_);
lean_dec_ref(v_vs_463_);
lean_dec_ref(v_ks_462_);
return v___x_466_;
}
else
{
return v_newNode_456_;
}
}
else
{
return v_newNode_456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(size_t v_depth_469_, lean_object* v_keys_470_, lean_object* v_vals_471_, lean_object* v_i_472_, lean_object* v_entries_473_){
_start:
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = lean_array_get_size(v_keys_470_);
v___x_475_ = lean_nat_dec_lt(v_i_472_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec(v_i_472_);
return v_entries_473_;
}
else
{
lean_object* v_k_476_; lean_object* v_v_477_; uint64_t v___x_478_; size_t v_h_479_; size_t v___x_480_; lean_object* v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v_h_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v_k_476_ = lean_array_fget_borrowed(v_keys_470_, v_i_472_);
v_v_477_ = lean_array_fget_borrowed(v_vals_471_, v_i_472_);
v___x_478_ = l_Lean_instHashableMVarId_hash(v_k_476_);
v_h_479_ = lean_uint64_to_usize(v___x_478_);
v___x_480_ = ((size_t)5ULL);
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_sub(v_depth_469_, v___x_482_);
v___x_484_ = lean_usize_mul(v___x_480_, v___x_483_);
v_h_485_ = lean_usize_shift_right(v_h_479_, v___x_484_);
v___x_486_ = lean_nat_add(v_i_472_, v___x_481_);
lean_dec(v_i_472_);
lean_inc(v_v_477_);
lean_inc(v_k_476_);
v___x_487_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_entries_473_, v_h_485_, v_depth_469_, v_k_476_, v_v_477_);
v_i_472_ = v___x_486_;
v_entries_473_ = v___x_487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_depth_489_, lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_i_492_, lean_object* v_entries_493_){
_start:
{
size_t v_depth_boxed_494_; lean_object* v_res_495_; 
v_depth_boxed_494_ = lean_unbox_usize(v_depth_489_);
lean_dec(v_depth_489_);
v_res_495_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_boxed_494_, v_keys_490_, v_vals_491_, v_i_492_, v_entries_493_);
lean_dec_ref(v_vals_491_);
lean_dec_ref(v_keys_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
size_t v_x_8843__boxed_501_; size_t v_x_8844__boxed_502_; lean_object* v_res_503_; 
v_x_8843__boxed_501_ = lean_unbox_usize(v_x_497_);
lean_dec(v_x_497_);
v_x_8844__boxed_502_ = lean_unbox_usize(v_x_498_);
lean_dec(v_x_498_);
v_res_503_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_496_, v_x_8843__boxed_501_, v_x_8844__boxed_502_, v_x_499_, v_x_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_){
_start:
{
uint64_t v___x_507_; size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; 
v___x_507_ = l_Lean_instHashableMVarId_hash(v_x_505_);
v___x_508_ = lean_uint64_to_usize(v___x_507_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_504_, v___x_508_, v___x_509_, v_x_505_, v_x_506_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object* v_mvarId_511_, lean_object* v_val_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; lean_object* v_mctx_516_; lean_object* v_cache_517_; lean_object* v_zetaDeltaFVarIds_518_; lean_object* v_postponed_519_; lean_object* v_diag_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_550_; 
v___x_515_ = lean_st_ref_take(v___y_513_);
v_mctx_516_ = lean_ctor_get(v___x_515_, 0);
v_cache_517_ = lean_ctor_get(v___x_515_, 1);
v_zetaDeltaFVarIds_518_ = lean_ctor_get(v___x_515_, 2);
v_postponed_519_ = lean_ctor_get(v___x_515_, 3);
v_diag_520_ = lean_ctor_get(v___x_515_, 4);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_550_ == 0)
{
v___x_522_ = v___x_515_;
v_isShared_523_ = v_isSharedCheck_550_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_diag_520_);
lean_inc(v_postponed_519_);
lean_inc(v_zetaDeltaFVarIds_518_);
lean_inc(v_cache_517_);
lean_inc(v_mctx_516_);
lean_dec(v___x_515_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_550_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_depth_524_; lean_object* v_levelAssignDepth_525_; lean_object* v_lmvarCounter_526_; lean_object* v_mvarCounter_527_; lean_object* v_lDecls_528_; lean_object* v_decls_529_; lean_object* v_userNames_530_; lean_object* v_lAssignment_531_; lean_object* v_eAssignment_532_; lean_object* v_dAssignment_533_; lean_object* v_instanceTypedMVars_534_; lean_object* v_synthNormMemo_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_549_; 
v_depth_524_ = lean_ctor_get(v_mctx_516_, 0);
v_levelAssignDepth_525_ = lean_ctor_get(v_mctx_516_, 1);
v_lmvarCounter_526_ = lean_ctor_get(v_mctx_516_, 2);
v_mvarCounter_527_ = lean_ctor_get(v_mctx_516_, 3);
v_lDecls_528_ = lean_ctor_get(v_mctx_516_, 4);
v_decls_529_ = lean_ctor_get(v_mctx_516_, 5);
v_userNames_530_ = lean_ctor_get(v_mctx_516_, 6);
v_lAssignment_531_ = lean_ctor_get(v_mctx_516_, 7);
v_eAssignment_532_ = lean_ctor_get(v_mctx_516_, 8);
v_dAssignment_533_ = lean_ctor_get(v_mctx_516_, 9);
v_instanceTypedMVars_534_ = lean_ctor_get(v_mctx_516_, 10);
v_synthNormMemo_535_ = lean_ctor_get(v_mctx_516_, 11);
v_isSharedCheck_549_ = !lean_is_exclusive(v_mctx_516_);
if (v_isSharedCheck_549_ == 0)
{
v___x_537_ = v_mctx_516_;
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_synthNormMemo_535_);
lean_inc(v_instanceTypedMVars_534_);
lean_inc(v_dAssignment_533_);
lean_inc(v_eAssignment_532_);
lean_inc(v_lAssignment_531_);
lean_inc(v_userNames_530_);
lean_inc(v_decls_529_);
lean_inc(v_lDecls_528_);
lean_inc(v_mvarCounter_527_);
lean_inc(v_lmvarCounter_526_);
lean_inc(v_levelAssignDepth_525_);
lean_inc(v_depth_524_);
lean_dec(v_mctx_516_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_539_ = lean_box(0);
v___x_540_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_532_, v_mvarId_511_, v_val_512_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 8, v___x_540_);
v___x_542_ = v___x_537_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_depth_524_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_levelAssignDepth_525_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_lmvarCounter_526_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_mvarCounter_527_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_lDecls_528_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v_decls_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_userNames_530_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_lAssignment_531_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 9, v_dAssignment_533_);
lean_ctor_set(v_reuseFailAlloc_548_, 10, v_instanceTypedMVars_534_);
lean_ctor_set(v_reuseFailAlloc_548_, 11, v_synthNormMemo_535_);
v___x_542_ = v_reuseFailAlloc_548_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_544_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_542_);
v___x_544_ = v___x_522_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_cache_517_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_zetaDeltaFVarIds_518_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_postponed_519_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_diag_520_);
v___x_544_ = v_reuseFailAlloc_547_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_st_ref_put(v___y_513_, v___x_544_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_539_);
return v___x_546_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object* v_mvarId_551_, lean_object* v_val_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_551_, v_val_552_, v___y_553_);
lean_dec(v___y_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object* v_msgData_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_){
_start:
{
lean_object* v___x_562_; lean_object* v_env_563_; uint8_t v___x_564_; lean_object* v_env_565_; lean_object* v___x_566_; lean_object* v_toCold_567_; lean_object* v_mctx_568_; lean_object* v_lctx_569_; lean_object* v_options_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_562_ = lean_st_ref_get(v___y_560_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_563_);
lean_dec(v___x_562_);
v___x_564_ = 0;
v_env_565_ = l_Lean_Environment_setRecordingDeps(v_env_563_, v___x_564_);
v___x_566_ = lean_st_ref_get(v___y_558_);
v_toCold_567_ = lean_ctor_get(v___y_559_, 0);
v_mctx_568_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_mctx_568_);
lean_dec(v___x_566_);
v_lctx_569_ = lean_ctor_get(v___y_557_, 2);
v_options_570_ = lean_ctor_get(v_toCold_567_, 2);
lean_inc_ref(v_options_570_);
lean_inc_ref(v_lctx_569_);
v___x_571_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_571_, 0, v_env_565_);
lean_ctor_set(v___x_571_, 1, v_mctx_568_);
lean_ctor_set(v___x_571_, 2, v_lctx_569_);
lean_ctor_set(v___x_571_, 3, v_options_570_);
v___x_572_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v_msgData_556_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_ref_587_; lean_object* v___x_588_; lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_597_; 
v_ref_587_ = lean_ctor_get(v___y_584_, 2);
v___x_588_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_597_ == 0)
{
v___x_591_ = v___x_588_;
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_597_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; lean_object* v___x_595_; 
lean_inc(v_ref_587_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_ref_587_);
lean_ctor_set(v___x_593_, 1, v_a_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 1);
lean_ctor_set(v___x_591_, 0, v___x_593_);
v___x_595_ = v___x_591_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___x_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_605_, lean_object* v_b_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_array_612_; lean_object* v_start_613_; lean_object* v_stop_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_629_; 
v_array_612_ = lean_ctor_get(v_a_605_, 0);
v_start_613_ = lean_ctor_get(v_a_605_, 1);
v_stop_614_ = lean_ctor_get(v_a_605_, 2);
v_isSharedCheck_629_ = !lean_is_exclusive(v_a_605_);
if (v_isSharedCheck_629_ == 0)
{
v___x_616_ = v_a_605_;
v_isShared_617_ = v_isSharedCheck_629_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_stop_614_);
lean_inc(v_start_613_);
lean_inc(v_array_612_);
lean_dec(v_a_605_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_629_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_lt(v_start_613_, v_stop_614_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; 
lean_del_object(v___x_616_);
lean_dec(v_stop_614_);
lean_dec(v_start_613_);
lean_dec_ref(v_array_612_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v_b_606_);
return v___x_619_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_start_613_, v___x_620_);
lean_inc_ref(v_array_612_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 1, v___x_621_);
v___x_623_ = v___x_616_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_array_612_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_stop_614_);
v___x_623_ = v_reuseFailAlloc_628_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_array_fget(v_array_612_, v_start_613_);
lean_dec(v_start_613_);
lean_dec_ref(v_array_612_);
v___x_625_ = l_Lean_Meta_mkCongrFun(v_b_606_, v___x_624_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_a_626_);
lean_dec_ref_known(v___x_625_, 1);
v_a_605_ = v___x_623_;
v_b_606_ = v_a_626_;
goto _start;
}
else
{
lean_dec_ref(v___x_623_);
return v___x_625_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_630_, lean_object* v_b_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_630_, v_b_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_638_, lean_object* v___x_639_, size_t v_sz_640_, size_t v_i_641_, lean_object* v_bs_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = lean_usize_dec_lt(v_i_641_, v_sz_640_);
if (v___x_643_ == 0)
{
lean_dec(v_levels_638_);
return v_bs_642_;
}
else
{
lean_object* v_v_644_; lean_object* v_toConstantVal_645_; lean_object* v_name_646_; lean_object* v___x_647_; lean_object* v_bs_x27_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
v_v_644_ = lean_array_uget_borrowed(v_bs_642_, v_i_641_);
v_toConstantVal_645_ = lean_ctor_get(v_v_644_, 0);
v_name_646_ = lean_ctor_get(v_toConstantVal_645_, 0);
lean_inc(v_name_646_);
v___x_647_ = lean_unsigned_to_nat(0u);
v_bs_x27_648_ = lean_array_uset(v_bs_642_, v_i_641_, v___x_647_);
v___x_649_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_646_);
lean_inc(v_levels_638_);
v___x_650_ = l_Lean_mkConst(v___x_649_, v_levels_638_);
v___x_651_ = l_Lean_mkAppN(v___x_650_, v___x_639_);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_add(v_i_641_, v___x_652_);
v___x_654_ = lean_array_uset(v_bs_x27_648_, v_i_641_, v___x_651_);
v_i_641_ = v___x_653_;
v_bs_642_ = v___x_654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_656_, lean_object* v___x_657_, lean_object* v_sz_658_, lean_object* v_i_659_, lean_object* v_bs_660_){
_start:
{
size_t v_sz_boxed_661_; size_t v_i_boxed_662_; lean_object* v_res_663_; 
v_sz_boxed_661_ = lean_unbox_usize(v_sz_658_);
lean_dec(v_sz_658_);
v_i_boxed_662_ = lean_unbox_usize(v_i_659_);
lean_dec(v_i_659_);
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_656_, v___x_657_, v_sz_boxed_661_, v_i_boxed_662_, v_bs_660_);
lean_dec_ref(v___x_657_);
return v_res_663_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0));
v___x_666_ = l_Lean_stringToMessageData(v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object* v_infos_670_, lean_object* v_numParams_671_, lean_object* v___x_672_, lean_object* v_name_673_, lean_object* v_levels_674_, lean_object* v_args_675_, lean_object* v_x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; size_t v_sz_700_; size_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_689_ = lean_array_get_size(v_infos_670_);
v___x_690_ = lean_nat_sub(v_numParams_671_, v___x_689_);
lean_inc(v___x_672_);
lean_inc_ref(v_args_675_);
v___x_691_ = l_Array_toSubarray___redArg(v_args_675_, v___x_672_, v___x_690_);
v___x_692_ = lean_array_get_size(v_args_675_);
v___x_693_ = l_Array_toSubarray___redArg(v_args_675_, v_numParams_671_, v___x_692_);
lean_inc_n(v_name_673_, 2);
v___x_694_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_673_);
lean_inc_n(v_levels_674_, 3);
lean_inc(v___x_694_);
v___x_695_ = l_Lean_mkConst(v___x_694_, v_levels_674_);
v___x_696_ = l_Subarray_copy___redArg(v___x_691_);
v___x_697_ = l_Lean_mkAppN(v___x_695_, v___x_696_);
lean_inc_ref(v___x_693_);
v___x_698_ = l_Subarray_copy___redArg(v___x_693_);
v___x_699_ = l_Lean_mkAppN(v___x_697_, v___x_698_);
v_sz_700_ = lean_array_size(v_infos_670_);
v___x_701_ = ((size_t)0ULL);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_674_, v___x_696_, v_sz_700_, v___x_701_, v_infos_670_);
v___x_703_ = l_Lean_mkConst(v_name_673_, v_levels_674_);
lean_inc_ref(v___x_696_);
v___x_704_ = l_Array_append___redArg(v___x_696_, v___x_702_);
lean_dec_ref(v___x_702_);
v___x_705_ = l_Array_append___redArg(v___x_704_, v___x_698_);
v___x_706_ = l_Lean_mkAppN(v___x_703_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = l_Lean_Meta_mkEq(v___x_699_, v___x_706_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_767_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_767_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_767_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_767_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 1);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_766_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = 0;
v___x_715_ = lean_box(0);
v___x_716_ = l_Lean_Meta_mkFreshExprMVar(v___x_713_, v___x_714_, v___x_715_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
v___x_718_ = l_Lean_Expr_mvarId_x21(v_a_717_);
v___x_719_ = l_Lean_Meta_getEqnsFor_x3f(v___x_694_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___x_719_, 1);
if (lean_obj_tag(v_a_720_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_val_721_ = lean_ctor_get(v_a_720_, 0);
lean_inc(v_val_721_);
lean_dec_ref_known(v_a_720_, 1);
v___x_722_ = lean_array_get_size(v_val_721_);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_val_721_);
lean_dec(v___x_718_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_693_);
lean_dec(v_levels_674_);
lean_dec(v_name_673_);
lean_dec(v___x_672_);
v___y_683_ = v___y_677_;
v___y_684_ = v___y_678_;
v___y_685_ = v___y_679_;
v___y_686_ = v___y_680_;
goto v___jp_682_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_725_ = lean_array_fget(v_val_721_, v___x_672_);
lean_dec(v___x_672_);
lean_dec(v_val_721_);
v___x_726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3));
v___x_727_ = l_Lean_Name_append(v_name_673_, v___x_726_);
lean_inc(v_levels_674_);
v___x_728_ = l_Lean_mkConst(v___x_727_, v_levels_674_);
v___x_729_ = l_Lean_mkConst(v___x_725_, v_levels_674_);
v___x_730_ = l_Lean_mkAppN(v___x_729_, v___x_696_);
v___x_731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_693_, v___x_730_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; uint8_t v___x_733_; lean_object* v___x_734_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = 0;
v___x_734_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_718_, v___x_728_, v___x_733_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_735_, v_a_732_, v___y_678_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v___x_737_; 
lean_dec_ref_known(v___x_736_, 1);
v___x_737_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_717_, v___y_678_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_a_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = l_Array_append___redArg(v___x_696_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_740_ = 1;
v___x_741_ = l_Lean_Meta_mkLambdaFVars(v___x_739_, v_a_738_, v___x_733_, v___x_724_, v___x_733_, v___x_724_, v___x_740_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___x_739_);
return v___x_741_;
}
else
{
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
return v___x_737_;
}
}
else
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_749_; 
lean_dec(v_a_717_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
v_a_742_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_749_ == 0)
{
v___x_744_ = v___x_736_;
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_736_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_749_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_a_742_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_a_732_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
v_a_750_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_734_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_734_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
else
{
lean_dec_ref(v___x_728_);
lean_dec(v___x_718_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
return v___x_731_;
}
}
}
else
{
lean_dec(v_a_720_);
lean_dec(v___x_718_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_693_);
lean_dec(v_levels_674_);
lean_dec(v_name_673_);
lean_dec(v___x_672_);
v___y_683_ = v___y_677_;
v___y_684_ = v___y_678_;
v___y_685_ = v___y_679_;
v___y_686_ = v___y_680_;
goto v___jp_682_;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v___x_718_);
lean_dec(v_a_717_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_693_);
lean_dec(v_levels_674_);
lean_dec(v_name_673_);
lean_dec(v___x_672_);
v_a_758_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_719_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_719_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec(v_levels_674_);
lean_dec(v_name_673_);
lean_dec(v___x_672_);
return v___x_716_;
}
}
}
}
else
{
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_696_);
lean_dec(v___x_694_);
lean_dec_ref(v___x_693_);
lean_dec(v_levels_674_);
lean_dec(v_name_673_);
lean_dec(v___x_672_);
return v___x_707_;
}
v___jp_682_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
v___x_688_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_687_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object* v_infos_768_, lean_object* v_numParams_769_, lean_object* v___x_770_, lean_object* v_name_771_, lean_object* v_levels_772_, lean_object* v_args_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_768_, v_numParams_769_, v___x_770_, v_name_771_, v_levels_772_, v_args_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec_ref(v_x_774_);
return v_res_780_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0(void){
_start:
{
lean_object* v___x_781_; double v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_float_of_nat(v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_786_, lean_object* v_msg_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
lean_object* v_ref_793_; lean_object* v___x_794_; lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_840_; 
v_ref_793_ = lean_ctor_get(v___y_790_, 2);
v___x_794_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_840_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_840_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_840_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v_traceState_800_; lean_object* v_env_801_; lean_object* v_nextMacroScope_802_; lean_object* v_ngen_803_; lean_object* v_auxDeclNGen_804_; lean_object* v_cache_805_; lean_object* v_recordedDeps_806_; lean_object* v_messages_807_; lean_object* v_infoState_808_; lean_object* v_snapshotTasks_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_839_; 
v___x_799_ = lean_st_ref_take(v___y_791_);
v_traceState_800_ = lean_ctor_get(v___x_799_, 4);
v_env_801_ = lean_ctor_get(v___x_799_, 0);
v_nextMacroScope_802_ = lean_ctor_get(v___x_799_, 1);
v_ngen_803_ = lean_ctor_get(v___x_799_, 2);
v_auxDeclNGen_804_ = lean_ctor_get(v___x_799_, 3);
v_cache_805_ = lean_ctor_get(v___x_799_, 5);
v_recordedDeps_806_ = lean_ctor_get(v___x_799_, 6);
v_messages_807_ = lean_ctor_get(v___x_799_, 7);
v_infoState_808_ = lean_ctor_get(v___x_799_, 8);
v_snapshotTasks_809_ = lean_ctor_get(v___x_799_, 9);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_839_ == 0)
{
v___x_811_ = v___x_799_;
v_isShared_812_ = v_isSharedCheck_839_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snapshotTasks_809_);
lean_inc(v_infoState_808_);
lean_inc(v_messages_807_);
lean_inc(v_recordedDeps_806_);
lean_inc(v_cache_805_);
lean_inc(v_traceState_800_);
lean_inc(v_auxDeclNGen_804_);
lean_inc(v_ngen_803_);
lean_inc(v_nextMacroScope_802_);
lean_inc(v_env_801_);
lean_dec(v___x_799_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_839_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint64_t v_tid_813_; lean_object* v_traces_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_838_; 
v_tid_813_ = lean_ctor_get_uint64(v_traceState_800_, sizeof(void*)*1);
v_traces_814_ = lean_ctor_get(v_traceState_800_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_traceState_800_);
if (v_isSharedCheck_838_ == 0)
{
v___x_816_ = v_traceState_800_;
v_isShared_817_ = v_isSharedCheck_838_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_traces_814_);
lean_dec(v_traceState_800_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_838_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; lean_object* v___x_819_; double v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_box(0);
v___x_820_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_821_ = 0;
v___x_822_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_823_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_823_, 0, v_cls_786_);
lean_ctor_set(v___x_823_, 1, v___x_819_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
lean_ctor_set_float(v___x_823_, sizeof(void*)*3, v___x_820_);
lean_ctor_set_float(v___x_823_, sizeof(void*)*3 + 8, v___x_820_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*3 + 16, v___x_821_);
v___x_824_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_825_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v_a_795_);
lean_ctor_set(v___x_825_, 2, v___x_824_);
lean_inc(v_ref_793_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v_ref_793_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_PersistentArray_push___redArg(v_traces_814_, v___x_826_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_827_);
v___x_829_ = v___x_816_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_827_);
lean_ctor_set_uint64(v_reuseFailAlloc_837_, sizeof(void*)*1, v_tid_813_);
v___x_829_ = v_reuseFailAlloc_837_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 4, v___x_829_);
v___x_831_ = v___x_811_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_env_801_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_nextMacroScope_802_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_ngen_803_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_auxDeclNGen_804_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 5, v_cache_805_);
lean_ctor_set(v_reuseFailAlloc_836_, 6, v_recordedDeps_806_);
lean_ctor_set(v_reuseFailAlloc_836_, 7, v_messages_807_);
lean_ctor_set(v_reuseFailAlloc_836_, 8, v_infoState_808_);
lean_ctor_set(v_reuseFailAlloc_836_, 9, v_snapshotTasks_809_);
v___x_831_ = v_reuseFailAlloc_836_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_832_ = lean_st_ref_put(v___y_791_, v___x_831_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_818_);
v___x_834_ = v___x_797_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_818_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object* v_cls_841_, lean_object* v_msg_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_841_, v_msg_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
return v_res_848_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_857_ = l_Lean_Name_append(v___x_856_, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object* v_infos_861_, lean_object* v_levels_862_, lean_object* v_as_863_, size_t v_sz_864_, size_t v_i_865_, lean_object* v_b_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v___x_872_; 
v___x_872_ = lean_usize_dec_lt(v_i_865_, v_sz_864_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; 
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v_b_866_);
return v___x_873_;
}
else
{
lean_object* v_a_874_; lean_object* v_toConstantVal_875_; lean_object* v_numParams_876_; lean_object* v_name_877_; lean_object* v_levelParams_878_; lean_object* v_type_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___f_882_; uint8_t v___x_883_; lean_object* v___x_884_; 
v_a_874_ = lean_array_uget_borrowed(v_as_863_, v_i_865_);
v_toConstantVal_875_ = lean_ctor_get(v_a_874_, 0);
v_numParams_876_ = lean_ctor_get(v_a_874_, 1);
v_name_877_ = lean_ctor_get(v_toConstantVal_875_, 0);
v_levelParams_878_ = lean_ctor_get(v_toConstantVal_875_, 1);
v_type_879_ = lean_ctor_get(v_toConstantVal_875_, 2);
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_box(0);
lean_inc(v_levels_862_);
lean_inc(v_name_877_);
lean_inc(v_numParams_876_);
lean_inc_ref(v_infos_861_);
v___f_882_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed), 12, 5);
lean_closure_set(v___f_882_, 0, v_infos_861_);
lean_closure_set(v___f_882_, 1, v_numParams_876_);
lean_closure_set(v___f_882_, 2, v___x_880_);
lean_closure_set(v___f_882_, 3, v_name_877_);
lean_closure_set(v___f_882_, 4, v_levels_862_);
v___x_883_ = 0;
lean_inc_ref(v_type_879_);
v___x_884_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_879_, v___f_882_, v___x_883_, v___x_883_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v_toCold_920_; lean_object* v_options_921_; uint8_t v_hasTrace_922_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v_toCold_920_ = lean_ctor_get(v___y_869_, 0);
v_options_921_ = lean_ctor_get(v_toCold_920_, 2);
v_hasTrace_922_ = lean_ctor_get_uint8(v_options_921_, sizeof(void*)*1);
if (v_hasTrace_922_ == 0)
{
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
v___y_889_ = v___y_869_;
v___y_890_ = v___y_870_;
goto v___jp_886_;
}
else
{
lean_object* v_inheritedTraceOptions_923_; lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_inheritedTraceOptions_923_ = lean_ctor_get(v_toCold_920_, 11);
v___x_924_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_925_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_926_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_923_, v_options_921_, v___x_925_);
if (v___x_926_ == 0)
{
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
v___y_889_ = v___y_869_;
v___y_890_ = v___y_870_;
goto v___jp_886_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
lean_inc(v_a_885_);
v___x_928_ = l_Lean_MessageData_ofExpr(v_a_885_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_924_, v___x_929_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_dec_ref_known(v___x_930_, 1);
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
v___y_889_ = v___y_869_;
v___y_890_ = v___y_870_;
goto v___jp_886_;
}
else
{
lean_dec(v_a_885_);
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
return v___x_930_;
}
}
}
v___jp_886_:
{
lean_object* v___x_891_; 
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v_a_885_);
v___x_891_ = lean_infer_type(v_a_885_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
lean_inc(v_name_877_);
v___x_893_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_877_);
v___x_894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_895_ = l_Lean_Name_append(v___x_893_, v___x_894_);
v___x_896_ = lean_box(0);
lean_inc(v_levelParams_878_);
v___x_897_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_895_, v_levelParams_878_, v_a_892_, v_a_885_, v___x_896_, v___y_890_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_a_898_);
v___x_900_ = l_Lean_addDecl(v___x_899_, v___x_883_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_900_) == 0)
{
size_t v___x_901_; size_t v___x_902_; 
lean_dec_ref_known(v___x_900_, 1);
v___x_901_ = ((size_t)1ULL);
v___x_902_ = lean_usize_add(v_i_865_, v___x_901_);
v_i_865_ = v___x_902_;
v_b_866_ = v___x_881_;
goto _start;
}
else
{
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
return v___x_900_;
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
v_a_904_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_897_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_897_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_a_885_);
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
v_a_912_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_891_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_891_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
v_a_931_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_884_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_884_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object* v_infos_939_, lean_object* v_levels_940_, lean_object* v_as_941_, lean_object* v_sz_942_, lean_object* v_i_943_, lean_object* v_b_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_){
_start:
{
size_t v_sz_boxed_950_; size_t v_i_boxed_951_; lean_object* v_res_952_; 
v_sz_boxed_950_ = lean_unbox_usize(v_sz_942_);
lean_dec(v_sz_942_);
v_i_boxed_951_ = lean_unbox_usize(v_i_943_);
lean_dec(v_i_943_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_939_, v_levels_940_, v_as_941_, v_sz_boxed_950_, v_i_boxed_951_, v_b_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec_ref(v_as_941_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object* v_infos_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v_toConstantVal_962_; lean_object* v_levelParams_963_; lean_object* v___x_964_; lean_object* v_levels_965_; lean_object* v___x_966_; size_t v_sz_967_; size_t v___x_968_; lean_object* v___x_969_; 
v___x_959_ = l_Lean_instInhabitedInductiveVal_default;
v___x_960_ = lean_unsigned_to_nat(0u);
v___x_961_ = lean_array_get_borrowed(v___x_959_, v_infos_953_, v___x_960_);
v_toConstantVal_962_ = lean_ctor_get(v___x_961_, 0);
v_levelParams_963_ = lean_ctor_get(v_toConstantVal_962_, 1);
v___x_964_ = lean_box(0);
lean_inc(v_levelParams_963_);
v_levels_965_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_963_, v___x_964_);
v___x_966_ = lean_box(0);
v_sz_967_ = lean_array_size(v_infos_953_);
v___x_968_ = ((size_t)0ULL);
lean_inc_ref(v_infos_953_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_953_, v_levels_965_, v_infos_953_, v_sz_967_, v___x_968_, v___x_966_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec_ref(v_infos_953_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v___x_969_, 0);
lean_dec(v_unused_977_);
v___x_971_ = v___x_969_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_dec(v___x_969_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 0, v___x_966_);
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_966_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
else
{
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object* v_infos_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object* v_00_u03b1_985_, lean_object* v_msg_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object* v_00_u03b1_993_, lean_object* v_msg_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_993_, v_msg_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object* v_inst_1001_, lean_object* v_R_1002_, lean_object* v_a_1003_, lean_object* v_b_1004_, lean_object* v_c_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_1003_, v_b_1004_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object* v_inst_1012_, lean_object* v_R_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_, lean_object* v_c_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_1012_, v_R_1013_, v_a_1014_, v_b_1015_, v_c_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object* v_mvarId_1023_, lean_object* v_val_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_1023_, v_val_1024_, v___y_1026_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object* v_mvarId_1031_, lean_object* v_val_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1031_, v_val_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object* v_00_u03b2_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_1040_, v_x_1041_, v_x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1044_, lean_object* v_x_1045_, size_t v_x_1046_, size_t v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_1045_, v_x_1046_, v_x_1047_, v_x_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
size_t v_x_9769__boxed_1057_; size_t v_x_9770__boxed_1058_; lean_object* v_res_1059_; 
v_x_9769__boxed_1057_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_x_9770__boxed_1058_ = lean_unbox_usize(v_x_1054_);
lean_dec(v_x_1054_);
v_res_1059_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_1051_, v_x_1052_, v_x_9769__boxed_1057_, v_x_9770__boxed_1058_, v_x_1055_, v_x_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1060_, lean_object* v_n_1061_, lean_object* v_k_1062_, lean_object* v_v_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v_n_1061_, v_k_1062_, v_v_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1065_, size_t v_depth_1066_, lean_object* v_keys_1067_, lean_object* v_vals_1068_, lean_object* v_heq_1069_, lean_object* v_i_1070_, lean_object* v_entries_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_1066_, v_keys_1067_, v_vals_1068_, v_i_1070_, v_entries_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1073_, lean_object* v_depth_1074_, lean_object* v_keys_1075_, lean_object* v_vals_1076_, lean_object* v_heq_1077_, lean_object* v_i_1078_, lean_object* v_entries_1079_){
_start:
{
size_t v_depth_boxed_1080_; lean_object* v_res_1081_; 
v_depth_boxed_1080_ = lean_unbox_usize(v_depth_1074_);
lean_dec(v_depth_1074_);
v_res_1081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(v_00_u03b2_1073_, v_depth_boxed_1080_, v_keys_1075_, v_vals_1076_, v_heq_1077_, v_i_1078_, v_entries_1079_);
lean_dec_ref(v_vals_1076_);
lean_dec_ref(v_keys_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_x_1083_, v_x_1084_, v_x_1085_, v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object* v_e_1088_, lean_object* v___y_1089_){
_start:
{
uint8_t v___x_1091_; 
v___x_1091_ = l_Lean_Expr_hasMVar(v_e_1088_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_e_1088_);
return v___x_1092_;
}
else
{
lean_object* v___x_1093_; lean_object* v_mctx_1094_; lean_object* v___x_1095_; lean_object* v_fst_1096_; lean_object* v_snd_1097_; lean_object* v___x_1098_; lean_object* v_cache_1099_; lean_object* v_zetaDeltaFVarIds_1100_; lean_object* v_postponed_1101_; lean_object* v_diag_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1111_; 
v___x_1093_ = lean_st_ref_get(v___y_1089_);
v_mctx_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc_ref(v_mctx_1094_);
lean_dec(v___x_1093_);
v___x_1095_ = l_Lean_instantiateMVarsCore(v_mctx_1094_, v_e_1088_);
v_fst_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_fst_1096_);
v_snd_1097_ = lean_ctor_get(v___x_1095_, 1);
lean_inc(v_snd_1097_);
lean_dec_ref(v___x_1095_);
v___x_1098_ = lean_st_ref_take(v___y_1089_);
v_cache_1099_ = lean_ctor_get(v___x_1098_, 1);
v_zetaDeltaFVarIds_1100_ = lean_ctor_get(v___x_1098_, 2);
v_postponed_1101_ = lean_ctor_get(v___x_1098_, 3);
v_diag_1102_ = lean_ctor_get(v___x_1098_, 4);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; 
v_unused_1112_ = lean_ctor_get(v___x_1098_, 0);
lean_dec(v_unused_1112_);
v___x_1104_ = v___x_1098_;
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_diag_1102_);
lean_inc(v_postponed_1101_);
lean_inc(v_zetaDeltaFVarIds_1100_);
lean_inc(v_cache_1099_);
lean_dec(v___x_1098_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1111_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_snd_1097_);
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_snd_1097_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_cache_1099_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_zetaDeltaFVarIds_1100_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_postponed_1101_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_diag_1102_);
v___x_1107_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_st_ref_put(v___y_1089_, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_fst_1096_);
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_e_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1113_, v___y_1114_);
lean_dec(v___y_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_e_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1117_, v___y_1121_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_e_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object* v_k_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v_b_1138_, lean_object* v_c_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; 
lean_inc(v___y_1143_);
lean_inc_ref(v___y_1142_);
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
v___x_1145_ = lean_apply_9(v_k_1135_, v_b_1138_, v_c_1139_, v___y_1136_, v___y_1137_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, lean_box(0));
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object* v_k_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v_b_1149_, lean_object* v_c_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1146_, v___y_1147_, v___y_1148_, v_b_1149_, v_c_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_type_1157_, lean_object* v_k_1158_, uint8_t v_cleanupAnnotations_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___f_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
v___f_1167_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1167_, 0, v_k_1158_);
lean_closure_set(v___f_1167_, 1, v___y_1160_);
lean_closure_set(v___f_1167_, 2, v___y_1161_);
v___x_1168_ = 0;
v___x_1169_ = lean_box(0);
v___x_1170_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1168_, v___x_1169_, v_type_1157_, v___f_1167_, v_cleanupAnnotations_1159_, v___x_1168_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1170_) == 0)
{
return v___x_1170_;
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1170_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_type_1179_, lean_object* v_k_1180_, lean_object* v_cleanupAnnotations_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1189_; lean_object* v_res_1190_; 
v_cleanupAnnotations_boxed_1189_ = lean_unbox(v_cleanupAnnotations_1181_);
v_res_1190_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1179_, v_k_1180_, v_cleanupAnnotations_boxed_1189_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_00_u03b1_1191_, lean_object* v_type_1192_, lean_object* v_k_1193_, uint8_t v_cleanupAnnotations_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1192_, v_k_1193_, v_cleanupAnnotations_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_00_u03b1_1203_, lean_object* v_type_1204_, lean_object* v_k_1205_, lean_object* v_cleanupAnnotations_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1214_; lean_object* v_res_1215_; 
v_cleanupAnnotations_boxed_1214_ = lean_unbox(v_cleanupAnnotations_1206_);
v_res_1215_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_1203_, v_type_1204_, v_k_1205_, v_cleanupAnnotations_boxed_1214_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_name_1216_, lean_object* v_levelParams_1217_, lean_object* v_type_1218_, lean_object* v_value_1219_, lean_object* v_hints_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v___x_1223_; uint8_t v___y_1225_; uint8_t v___y_1232_; lean_object* v_env_1235_; uint8_t v___x_1236_; 
v___x_1223_ = lean_st_ref_get(v___y_1221_);
v_env_1235_ = lean_ctor_get(v___x_1223_, 0);
lean_inc_ref_n(v_env_1235_, 2);
lean_dec(v___x_1223_);
v___x_1236_ = l_Lean_Environment_hasUnsafe(v_env_1235_, v_type_1218_);
if (v___x_1236_ == 0)
{
uint8_t v___x_1237_; 
v___x_1237_ = l_Lean_Environment_hasUnsafe(v_env_1235_, v_value_1219_);
v___y_1232_ = v___x_1237_;
goto v___jp_1231_;
}
else
{
lean_dec_ref(v_env_1235_);
v___y_1232_ = v___x_1236_;
goto v___jp_1231_;
}
v___jp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
lean_inc(v_name_1216_);
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v_name_1216_);
lean_ctor_set(v___x_1226_, 1, v_levelParams_1217_);
lean_ctor_set(v___x_1226_, 2, v_type_1218_);
v___x_1227_ = lean_box(0);
v___x_1228_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_name_1216_);
lean_ctor_set(v___x_1228_, 1, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
lean_ctor_set(v___x_1229_, 1, v_value_1219_);
lean_ctor_set(v___x_1229_, 2, v_hints_1220_);
lean_ctor_set(v___x_1229_, 3, v___x_1228_);
lean_ctor_set_uint8(v___x_1229_, sizeof(void*)*4, v___y_1225_);
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v___x_1229_);
return v___x_1230_;
}
v___jp_1231_:
{
if (v___y_1232_ == 0)
{
uint8_t v___x_1233_; 
v___x_1233_ = 1;
v___y_1225_ = v___x_1233_;
goto v___jp_1224_;
}
else
{
uint8_t v___x_1234_; 
v___x_1234_ = 0;
v___y_1225_ = v___x_1234_;
goto v___jp_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1238_, lean_object* v_levelParams_1239_, lean_object* v_type_1240_, lean_object* v_value_1241_, lean_object* v_hints_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1238_, v_levelParams_1239_, v_type_1240_, v_value_1241_, v_hints_1242_, v___y_1243_);
lean_dec(v___y_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1246_, lean_object* v_levelParams_1247_, lean_object* v_type_1248_, lean_object* v_value_1249_, lean_object* v_hints_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1246_, v_levelParams_1247_, v_type_1248_, v_value_1249_, v_hints_1250_, v___y_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1259_, lean_object* v_levelParams_1260_, lean_object* v_type_1261_, lean_object* v_value_1262_, lean_object* v_hints_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1259_, v_levelParams_1260_, v_type_1261_, v_value_1262_, v_hints_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1272_, lean_object* v_maxFVars_x3f_1273_, lean_object* v_k_1274_, uint8_t v_cleanupAnnotations_1275_, uint8_t v_whnfType_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
lean_object* v___f_1284_; lean_object* v___x_1285_; 
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
v___f_1284_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1284_, 0, v_k_1274_);
lean_closure_set(v___f_1284_, 1, v___y_1277_);
lean_closure_set(v___f_1284_, 2, v___y_1278_);
v___x_1285_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1272_, v_maxFVars_x3f_1273_, v___f_1284_, v_cleanupAnnotations_1275_, v_whnfType_1276_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
if (lean_obj_tag(v___x_1285_) == 0)
{
return v___x_1285_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1294_, lean_object* v_maxFVars_x3f_1295_, lean_object* v_k_1296_, lean_object* v_cleanupAnnotations_1297_, lean_object* v_whnfType_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1306_; uint8_t v_whnfType_boxed_1307_; lean_object* v_res_1308_; 
v_cleanupAnnotations_boxed_1306_ = lean_unbox(v_cleanupAnnotations_1297_);
v_whnfType_boxed_1307_ = lean_unbox(v_whnfType_1298_);
v_res_1308_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1294_, v_maxFVars_x3f_1295_, v_k_1296_, v_cleanupAnnotations_boxed_1306_, v_whnfType_boxed_1307_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1309_, lean_object* v_type_1310_, lean_object* v_maxFVars_x3f_1311_, lean_object* v_k_1312_, uint8_t v_cleanupAnnotations_1313_, uint8_t v_whnfType_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1310_, v_maxFVars_x3f_1311_, v_k_1312_, v_cleanupAnnotations_1313_, v_whnfType_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_type_1324_, lean_object* v_maxFVars_x3f_1325_, lean_object* v_k_1326_, lean_object* v_cleanupAnnotations_1327_, lean_object* v_whnfType_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1336_; uint8_t v_whnfType_boxed_1337_; lean_object* v_res_1338_; 
v_cleanupAnnotations_boxed_1336_ = lean_unbox(v_cleanupAnnotations_1327_);
v_whnfType_boxed_1337_ = lean_unbox(v_whnfType_1328_);
v_res_1338_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1323_, v_type_1324_, v_maxFVars_x3f_1325_, v_k_1326_, v_cleanupAnnotations_boxed_1336_, v_whnfType_boxed_1337_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_toCold_1347_; lean_object* v_options_1348_; uint8_t v_hasTrace_1349_; 
v_toCold_1347_ = lean_ctor_get(v___y_1344_, 0);
v_options_1348_ = lean_ctor_get(v_toCold_1347_, 2);
v_hasTrace_1349_ = lean_ctor_get_uint8(v_options_1348_, sizeof(void*)*1);
if (v_hasTrace_1349_ == 0)
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
lean_dec(v_cls_1339_);
v___x_1350_ = lean_box(v_hasTrace_1349_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
else
{
lean_object* v_inheritedTraceOptions_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v_inheritedTraceOptions_1352_ = lean_ctor_get(v_toCold_1347_, 11);
v___x_1353_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1354_ = l_Lean_Name_append(v___x_1353_, v_cls_1339_);
v___x_1355_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1352_, v_options_1348_, v___x_1354_);
lean_dec(v___x_1354_);
v___x_1356_ = lean_box(v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object* v_cls_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_mvarId_1367_, lean_object* v_val_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; lean_object* v_mctx_1372_; lean_object* v_cache_1373_; lean_object* v_zetaDeltaFVarIds_1374_; lean_object* v_postponed_1375_; lean_object* v_diag_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1406_; 
v___x_1371_ = lean_st_ref_take(v___y_1369_);
v_mctx_1372_ = lean_ctor_get(v___x_1371_, 0);
v_cache_1373_ = lean_ctor_get(v___x_1371_, 1);
v_zetaDeltaFVarIds_1374_ = lean_ctor_get(v___x_1371_, 2);
v_postponed_1375_ = lean_ctor_get(v___x_1371_, 3);
v_diag_1376_ = lean_ctor_get(v___x_1371_, 4);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1378_ = v___x_1371_;
v_isShared_1379_ = v_isSharedCheck_1406_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_diag_1376_);
lean_inc(v_postponed_1375_);
lean_inc(v_zetaDeltaFVarIds_1374_);
lean_inc(v_cache_1373_);
lean_inc(v_mctx_1372_);
lean_dec(v___x_1371_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1406_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v_depth_1380_; lean_object* v_levelAssignDepth_1381_; lean_object* v_lmvarCounter_1382_; lean_object* v_mvarCounter_1383_; lean_object* v_lDecls_1384_; lean_object* v_decls_1385_; lean_object* v_userNames_1386_; lean_object* v_lAssignment_1387_; lean_object* v_eAssignment_1388_; lean_object* v_dAssignment_1389_; lean_object* v_instanceTypedMVars_1390_; lean_object* v_synthNormMemo_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1405_; 
v_depth_1380_ = lean_ctor_get(v_mctx_1372_, 0);
v_levelAssignDepth_1381_ = lean_ctor_get(v_mctx_1372_, 1);
v_lmvarCounter_1382_ = lean_ctor_get(v_mctx_1372_, 2);
v_mvarCounter_1383_ = lean_ctor_get(v_mctx_1372_, 3);
v_lDecls_1384_ = lean_ctor_get(v_mctx_1372_, 4);
v_decls_1385_ = lean_ctor_get(v_mctx_1372_, 5);
v_userNames_1386_ = lean_ctor_get(v_mctx_1372_, 6);
v_lAssignment_1387_ = lean_ctor_get(v_mctx_1372_, 7);
v_eAssignment_1388_ = lean_ctor_get(v_mctx_1372_, 8);
v_dAssignment_1389_ = lean_ctor_get(v_mctx_1372_, 9);
v_instanceTypedMVars_1390_ = lean_ctor_get(v_mctx_1372_, 10);
v_synthNormMemo_1391_ = lean_ctor_get(v_mctx_1372_, 11);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_mctx_1372_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1393_ = v_mctx_1372_;
v_isShared_1394_ = v_isSharedCheck_1405_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_synthNormMemo_1391_);
lean_inc(v_instanceTypedMVars_1390_);
lean_inc(v_dAssignment_1389_);
lean_inc(v_eAssignment_1388_);
lean_inc(v_lAssignment_1387_);
lean_inc(v_userNames_1386_);
lean_inc(v_decls_1385_);
lean_inc(v_lDecls_1384_);
lean_inc(v_mvarCounter_1383_);
lean_inc(v_lmvarCounter_1382_);
lean_inc(v_levelAssignDepth_1381_);
lean_inc(v_depth_1380_);
lean_dec(v_mctx_1372_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1405_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1395_ = lean_box(0);
v___x_1396_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1388_, v_mvarId_1367_, v_val_1368_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 8, v___x_1396_);
v___x_1398_ = v___x_1393_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_depth_1380_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_levelAssignDepth_1381_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_lmvarCounter_1382_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_mvarCounter_1383_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_lDecls_1384_);
lean_ctor_set(v_reuseFailAlloc_1404_, 5, v_decls_1385_);
lean_ctor_set(v_reuseFailAlloc_1404_, 6, v_userNames_1386_);
lean_ctor_set(v_reuseFailAlloc_1404_, 7, v_lAssignment_1387_);
lean_ctor_set(v_reuseFailAlloc_1404_, 8, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1404_, 9, v_dAssignment_1389_);
lean_ctor_set(v_reuseFailAlloc_1404_, 10, v_instanceTypedMVars_1390_);
lean_ctor_set(v_reuseFailAlloc_1404_, 11, v_synthNormMemo_1391_);
v___x_1398_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1398_);
v___x_1400_ = v___x_1378_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_cache_1373_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_zetaDeltaFVarIds_1374_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_postponed_1375_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_diag_1376_);
v___x_1400_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1401_ = lean_st_ref_put(v___y_1369_, v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1395_);
return v___x_1402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_mvarId_1407_, lean_object* v_val_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1407_, v_val_1408_, v___y_1409_);
lean_dec(v___y_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_cls_1412_, lean_object* v_msg_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_ref_1419_; lean_object* v___x_1420_; lean_object* v_a_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1466_; 
v_ref_1419_ = lean_ctor_get(v___y_1416_, 2);
v___x_1420_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1423_ = v___x_1420_;
v_isShared_1424_ = v_isSharedCheck_1466_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_a_1421_);
lean_dec(v___x_1420_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1466_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v_traceState_1426_; lean_object* v_env_1427_; lean_object* v_nextMacroScope_1428_; lean_object* v_ngen_1429_; lean_object* v_auxDeclNGen_1430_; lean_object* v_cache_1431_; lean_object* v_recordedDeps_1432_; lean_object* v_messages_1433_; lean_object* v_infoState_1434_; lean_object* v_snapshotTasks_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1465_; 
v___x_1425_ = lean_st_ref_take(v___y_1417_);
v_traceState_1426_ = lean_ctor_get(v___x_1425_, 4);
v_env_1427_ = lean_ctor_get(v___x_1425_, 0);
v_nextMacroScope_1428_ = lean_ctor_get(v___x_1425_, 1);
v_ngen_1429_ = lean_ctor_get(v___x_1425_, 2);
v_auxDeclNGen_1430_ = lean_ctor_get(v___x_1425_, 3);
v_cache_1431_ = lean_ctor_get(v___x_1425_, 5);
v_recordedDeps_1432_ = lean_ctor_get(v___x_1425_, 6);
v_messages_1433_ = lean_ctor_get(v___x_1425_, 7);
v_infoState_1434_ = lean_ctor_get(v___x_1425_, 8);
v_snapshotTasks_1435_ = lean_ctor_get(v___x_1425_, 9);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1425_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1437_ = v___x_1425_;
v_isShared_1438_ = v_isSharedCheck_1465_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_snapshotTasks_1435_);
lean_inc(v_infoState_1434_);
lean_inc(v_messages_1433_);
lean_inc(v_recordedDeps_1432_);
lean_inc(v_cache_1431_);
lean_inc(v_traceState_1426_);
lean_inc(v_auxDeclNGen_1430_);
lean_inc(v_ngen_1429_);
lean_inc(v_nextMacroScope_1428_);
lean_inc(v_env_1427_);
lean_dec(v___x_1425_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1465_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
uint64_t v_tid_1439_; lean_object* v_traces_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1464_; 
v_tid_1439_ = lean_ctor_get_uint64(v_traceState_1426_, sizeof(void*)*1);
v_traces_1440_ = lean_ctor_get(v_traceState_1426_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_traceState_1426_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1442_ = v_traceState_1426_;
v_isShared_1443_ = v_isSharedCheck_1464_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_traces_1440_);
lean_dec(v_traceState_1426_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1464_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; double v___x_1446_; uint8_t v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_1447_ = 0;
v___x_1448_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_1449_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1449_, 0, v_cls_1412_);
lean_ctor_set(v___x_1449_, 1, v___x_1445_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
lean_ctor_set_float(v___x_1449_, sizeof(void*)*3, v___x_1446_);
lean_ctor_set_float(v___x_1449_, sizeof(void*)*3 + 8, v___x_1446_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*3 + 16, v___x_1447_);
v___x_1450_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_1451_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1449_);
lean_ctor_set(v___x_1451_, 1, v_a_1421_);
lean_ctor_set(v___x_1451_, 2, v___x_1450_);
lean_inc(v_ref_1419_);
v___x_1452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1452_, 0, v_ref_1419_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = l_Lean_PersistentArray_push___redArg(v_traces_1440_, v___x_1452_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1453_);
v___x_1455_ = v___x_1442_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1453_);
lean_ctor_set_uint64(v_reuseFailAlloc_1463_, sizeof(void*)*1, v_tid_1439_);
v___x_1455_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1457_; 
if (v_isShared_1438_ == 0)
{
lean_ctor_set(v___x_1437_, 4, v___x_1455_);
v___x_1457_ = v___x_1437_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_env_1427_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_nextMacroScope_1428_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_ngen_1429_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_auxDeclNGen_1430_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1462_, 5, v_cache_1431_);
lean_ctor_set(v_reuseFailAlloc_1462_, 6, v_recordedDeps_1432_);
lean_ctor_set(v_reuseFailAlloc_1462_, 7, v_messages_1433_);
lean_ctor_set(v_reuseFailAlloc_1462_, 8, v_infoState_1434_);
lean_ctor_set(v_reuseFailAlloc_1462_, 9, v_snapshotTasks_1435_);
v___x_1457_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_st_ref_put(v___y_1417_, v___x_1457_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 0, v___x_1444_);
v___x_1460_ = v___x_1423_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1444_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_cls_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1467_, v_msg_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
return v_res_1474_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1475_; lean_object* v_dummy_1476_; 
v___x_1475_ = lean_box(0);
v_dummy_1476_ = l_Lean_Expr_sort___override(v___x_1475_);
return v_dummy_1476_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1));
v___x_1479_ = l_Lean_stringToMessageData(v___x_1478_);
return v___x_1479_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3));
v___x_1482_ = l_Lean_stringToMessageData(v___x_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v_numParams_1483_, lean_object* v___x_1484_, lean_object* v_name_1485_, lean_object* v___x_1486_, lean_object* v___x_1487_, lean_object* v_name_1488_, lean_object* v___x_1489_, lean_object* v_cls_1490_, lean_object* v_fields_1491_, lean_object* v_bodyExpr_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_toCold_1500_; lean_object* v_options_1501_; lean_object* v_inheritedTraceOptions_1502_; uint8_t v_hasTrace_1503_; lean_object* v_nargs_1504_; lean_object* v_dummy_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; 
v_toCold_1500_ = lean_ctor_get(v___y_1497_, 0);
v_options_1501_ = lean_ctor_get(v_toCold_1500_, 2);
v_inheritedTraceOptions_1502_ = lean_ctor_get(v_toCold_1500_, 11);
v_hasTrace_1503_ = lean_ctor_get_uint8(v_options_1501_, sizeof(void*)*1);
v_nargs_1504_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1492_);
v_dummy_1505_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
lean_inc(v_nargs_1504_);
v___x_1506_ = lean_mk_array(v_nargs_1504_, v_dummy_1505_);
v___x_1507_ = lean_unsigned_to_nat(1u);
v___x_1508_ = lean_nat_sub(v_nargs_1504_, v___x_1507_);
lean_dec(v_nargs_1504_);
v___x_1509_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1492_, v___x_1506_, v___x_1508_);
v___x_1510_ = lean_array_get_size(v___x_1509_);
v___x_1511_ = lean_nat_add(v_numParams_1483_, v___x_1484_);
v___x_1512_ = l_Array_toSubarray___redArg(v___x_1509_, v___x_1511_, v___x_1510_);
v___x_1513_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1485_);
lean_inc(v___x_1486_);
lean_inc(v___x_1513_);
v___x_1514_ = l_Lean_mkConst(v___x_1513_, v___x_1486_);
v___x_1515_ = l_Lean_mkAppN(v___x_1514_, v___x_1487_);
v___x_1516_ = l_Subarray_copy___redArg(v___x_1512_);
v___x_1517_ = l_Lean_mkAppN(v___x_1515_, v___x_1516_);
lean_dec_ref(v___x_1516_);
if (v_hasTrace_1503_ == 0)
{
lean_dec(v_cls_1490_);
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
v___y_1521_ = v___y_1495_;
v___y_1522_ = v___y_1496_;
v___y_1523_ = v___y_1497_;
v___y_1524_ = v___y_1498_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
lean_inc(v_cls_1490_);
v___x_1574_ = l_Lean_Name_append(v___x_1573_, v_cls_1490_);
v___x_1575_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1502_, v_options_1501_, v___x_1574_);
lean_dec(v___x_1574_);
if (v___x_1575_ == 0)
{
lean_dec(v_cls_1490_);
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
v___y_1521_ = v___y_1495_;
v___y_1522_ = v___y_1496_;
v___y_1523_ = v___y_1497_;
v___y_1524_ = v___y_1498_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1576_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
lean_inc(v_name_1488_);
v___x_1577_ = l_Lean_MessageData_ofName(v_name_1488_);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
v___x_1580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
lean_inc_ref(v___x_1517_);
v___x_1581_ = l_Lean_MessageData_ofExpr(v___x_1517_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1580_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1490_, v___x_1582_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_dec_ref_known(v___x_1583_, 1);
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
v___y_1521_ = v___y_1495_;
v___y_1522_ = v___y_1496_;
v___y_1523_ = v___y_1497_;
v___y_1524_ = v___y_1498_;
goto v___jp_1518_;
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec_ref(v___x_1517_);
lean_dec(v___x_1513_);
lean_dec(v_name_1488_);
lean_dec(v___x_1486_);
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
v___jp_1518_:
{
lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1517_);
v___x_1526_ = 0;
v___x_1527_ = lean_box(0);
v___x_1528_ = l_Lean_Meta_mkFreshExprMVar(v___x_1525_, v___x_1526_, v___x_1527_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = l_Lean_Expr_mvarId_x21(v_a_1529_);
v___x_1531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1532_ = l_Lean_Name_append(v___x_1513_, v___x_1531_);
lean_inc(v___x_1486_);
v___x_1533_ = l_Lean_mkConst(v___x_1532_, v___x_1486_);
v___x_1534_ = l_Lean_mkAppN(v___x_1533_, v___x_1487_);
lean_inc(v___x_1530_);
v___x_1535_ = l_Lean_MVarId_getType(v___x_1530_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; uint8_t v___x_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = 0;
v___x_1538_ = 1;
v___x_1539_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1530_);
v___x_1540_ = l_Lean_MVarId_rewrite(v___x_1530_, v_a_1536_, v___x_1534_, v___x_1537_, v___x_1539_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v_eNew_1542_; lean_object* v_eqProof_1543_; lean_object* v___x_1544_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v_eNew_1542_ = lean_ctor_get(v_a_1541_, 0);
lean_inc_ref(v_eNew_1542_);
v_eqProof_1543_ = lean_ctor_get(v_a_1541_, 1);
lean_inc_ref(v_eqProof_1543_);
lean_dec(v_a_1541_);
v___x_1544_ = l_Lean_MVarId_replaceTargetEq(v___x_1530_, v_eNew_1542_, v_eqProof_1543_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v_a_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v___x_1546_ = l_Lean_mkConst(v_name_1488_, v___x_1486_);
v___x_1547_ = l_Lean_mkAppN(v___x_1546_, v___x_1487_);
v___x_1548_ = l_Lean_mkAppN(v___x_1547_, v___x_1489_);
v___x_1549_ = l_Lean_mkAppN(v___x_1548_, v_fields_1491_);
v___x_1550_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_1545_, v___x_1549_, v___y_1522_);
lean_dec_ref(v___x_1550_);
v___x_1551_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1529_, v___y_1522_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
v___x_1553_ = 1;
v___x_1554_ = l_Lean_Meta_mkLambdaFVars(v_fields_1491_, v_a_1552_, v___x_1537_, v___x_1538_, v___x_1537_, v___x_1538_, v___x_1553_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = l_Lean_Meta_mkLambdaFVars(v___x_1487_, v_a_1555_, v___x_1537_, v___x_1538_, v___x_1537_, v___x_1538_, v___x_1553_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
return v___x_1556_;
}
else
{
return v___x_1554_;
}
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec(v_a_1529_);
lean_dec(v_name_1488_);
lean_dec(v___x_1486_);
v_a_1557_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1544_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1544_);
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
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v___x_1530_);
lean_dec(v_a_1529_);
lean_dec(v_name_1488_);
lean_dec(v___x_1486_);
v_a_1565_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1540_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1540_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_dec_ref(v___x_1534_);
lean_dec(v___x_1530_);
lean_dec(v_a_1529_);
lean_dec(v_name_1488_);
lean_dec(v___x_1486_);
return v___x_1535_;
}
}
else
{
lean_dec(v___x_1513_);
lean_dec(v_name_1488_);
lean_dec(v___x_1486_);
return v___x_1528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_1592_ = _args[0];
lean_object* v___x_1593_ = _args[1];
lean_object* v_name_1594_ = _args[2];
lean_object* v___x_1595_ = _args[3];
lean_object* v___x_1596_ = _args[4];
lean_object* v_name_1597_ = _args[5];
lean_object* v___x_1598_ = _args[6];
lean_object* v_cls_1599_ = _args[7];
lean_object* v_fields_1600_ = _args[8];
lean_object* v_bodyExpr_1601_ = _args[9];
lean_object* v___y_1602_ = _args[10];
lean_object* v___y_1603_ = _args[11];
lean_object* v___y_1604_ = _args[12];
lean_object* v___y_1605_ = _args[13];
lean_object* v___y_1606_ = _args[14];
lean_object* v___y_1607_ = _args[15];
lean_object* v___y_1608_ = _args[16];
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1592_, v___x_1593_, v_name_1594_, v___x_1595_, v___x_1596_, v_name_1597_, v___x_1598_, v_cls_1599_, v_fields_1600_, v_bodyExpr_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec_ref(v_fields_1600_);
lean_dec_ref(v___x_1598_);
lean_dec_ref(v___x_1596_);
lean_dec(v___x_1593_);
lean_dec(v_numParams_1592_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1610_, size_t v_sz_1611_, size_t v_i_1612_, lean_object* v_bs_1613_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = lean_usize_dec_lt(v_i_1612_, v_sz_1611_);
if (v___x_1614_ == 0)
{
return v_bs_1613_;
}
else
{
lean_object* v_v_1615_; lean_object* v___x_1616_; lean_object* v_bs_x27_1617_; lean_object* v___x_1618_; size_t v___x_1619_; size_t v___x_1620_; lean_object* v___x_1621_; 
v_v_1615_ = lean_array_uget(v_bs_1613_, v_i_1612_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v_bs_x27_1617_ = lean_array_uset(v_bs_1613_, v_i_1612_, v___x_1616_);
v___x_1618_ = l_Lean_mkAppN(v_v_1615_, v___x_1610_);
v___x_1619_ = ((size_t)1ULL);
v___x_1620_ = lean_usize_add(v_i_1612_, v___x_1619_);
v___x_1621_ = lean_array_uset(v_bs_x27_1617_, v_i_1612_, v___x_1618_);
v_i_1612_ = v___x_1620_;
v_bs_1613_ = v___x_1621_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1623_, lean_object* v_sz_1624_, lean_object* v_i_1625_, lean_object* v_bs_1626_){
_start:
{
size_t v_sz_boxed_1627_; size_t v_i_boxed_1628_; lean_object* v_res_1629_; 
v_sz_boxed_1627_ = lean_unbox_usize(v_sz_1624_);
lean_dec(v_sz_1624_);
v_i_boxed_1628_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_res_1629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1623_, v_sz_boxed_1627_, v_i_boxed_1628_, v_bs_1626_);
lean_dec_ref(v___x_1623_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1630_, size_t v_sz_1631_, size_t v_i_1632_, lean_object* v_bs_1633_){
_start:
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_usize_dec_lt(v_i_1632_, v_sz_1631_);
if (v___x_1634_ == 0)
{
lean_dec(v___x_1630_);
return v_bs_1633_;
}
else
{
lean_object* v_v_1635_; lean_object* v___x_1636_; lean_object* v_bs_x27_1637_; lean_object* v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v_v_1635_ = lean_array_uget(v_bs_1633_, v_i_1632_);
v___x_1636_ = lean_unsigned_to_nat(0u);
v_bs_x27_1637_ = lean_array_uset(v_bs_1633_, v_i_1632_, v___x_1636_);
lean_inc(v___x_1630_);
v___x_1638_ = l_Lean_mkConst(v_v_1635_, v___x_1630_);
v___x_1639_ = ((size_t)1ULL);
v___x_1640_ = lean_usize_add(v_i_1632_, v___x_1639_);
v___x_1641_ = lean_array_uset(v_bs_x27_1637_, v_i_1632_, v___x_1638_);
v_i_1632_ = v___x_1640_;
v_bs_1633_ = v___x_1641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1643_, lean_object* v_sz_1644_, lean_object* v_i_1645_, lean_object* v_bs_1646_){
_start:
{
size_t v_sz_boxed_1647_; size_t v_i_boxed_1648_; lean_object* v_res_1649_; 
v_sz_boxed_1647_ = lean_unbox_usize(v_sz_1644_);
lean_dec(v_sz_1644_);
v_i_boxed_1648_ = lean_unbox_usize(v_i_1645_);
lean_dec(v_i_1645_);
v_res_1649_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1643_, v_sz_boxed_1647_, v_i_boxed_1648_, v_bs_1646_);
return v_res_1649_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object* v___x_1653_, lean_object* v_numParams_1654_, lean_object* v___x_1655_, lean_object* v___x_1656_, size_t v___x_1657_, lean_object* v___x_1658_, lean_object* v_name_1659_, lean_object* v_name_1660_, lean_object* v_cls_1661_, lean_object* v_levelParams_1662_, lean_object* v_ctorSyntax_1663_, lean_object* v___f_1664_, lean_object* v_args_1665_, lean_object* v_body_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; size_t v_sz_1677_; lean_object* v___x_1678_; size_t v_sz_1679_; lean_object* v___x_1680_; lean_object* v___f_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v___x_1684_; lean_object* v___x_1685_; 
lean_inc_n(v_numParams_1654_, 2);
v___x_1674_ = l_Array_extract___redArg(v_args_1665_, v___x_1653_, v_numParams_1654_);
v___x_1675_ = lean_array_get_size(v_args_1665_);
v___x_1676_ = l_Array_toSubarray___redArg(v_args_1665_, v_numParams_1654_, v___x_1675_);
v_sz_1677_ = lean_array_size(v___x_1655_);
lean_inc(v___x_1656_);
v___x_1678_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1656_, v_sz_1677_, v___x_1657_, v___x_1655_);
v_sz_1679_ = lean_array_size(v___x_1678_);
v___x_1680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1674_, v_sz_1679_, v___x_1657_, v___x_1678_);
lean_inc(v_cls_1661_);
lean_inc_ref(v___x_1680_);
lean_inc(v_name_1660_);
v___f_1681_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1681_, 0, v_numParams_1654_);
lean_closure_set(v___f_1681_, 1, v___x_1658_);
lean_closure_set(v___f_1681_, 2, v_name_1659_);
lean_closure_set(v___f_1681_, 3, v___x_1656_);
lean_closure_set(v___f_1681_, 4, v___x_1674_);
lean_closure_set(v___f_1681_, 5, v_name_1660_);
lean_closure_set(v___f_1681_, 6, v___x_1680_);
lean_closure_set(v___f_1681_, 7, v_cls_1661_);
v___x_1682_ = l_Subarray_copy___redArg(v___x_1676_);
v___x_1683_ = l_Lean_Expr_replaceFVars(v_body_1666_, v___x_1682_, v___x_1680_);
lean_dec_ref(v___x_1680_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = 0;
v___x_1685_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_1683_, v___f_1681_, v___x_1684_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc_n(v_a_1686_, 2);
lean_dec_ref_known(v___x_1685_, 1);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
v___x_1687_ = lean_infer_type(v_a_1686_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; lean_object* v___y_1694_; lean_object* v___y_1695_; lean_object* v___x_1712_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref_known(v___x_1687_, 1);
lean_inc(v___y_1672_);
lean_inc_ref(v___y_1671_);
lean_inc(v___y_1670_);
lean_inc_ref(v___y_1669_);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
v___x_1712_ = lean_apply_7(v___f_1664_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, lean_box(0));
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; uint8_t v___x_1714_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v___x_1714_ = lean_unbox(v_a_1713_);
lean_dec(v_a_1713_);
if (v___x_1714_ == 0)
{
lean_dec(v_cls_1661_);
v___y_1690_ = v___y_1667_;
v___y_1691_ = v___y_1668_;
v___y_1692_ = v___y_1669_;
v___y_1693_ = v___y_1670_;
v___y_1694_ = v___y_1671_;
v___y_1695_ = v___y_1672_;
goto v___jp_1689_;
}
else
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
lean_inc(v_a_1688_);
v___x_1716_ = l_Lean_MessageData_ofExpr(v_a_1688_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1715_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1661_, v___x_1717_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_dec_ref_known(v___x_1718_, 1);
v___y_1690_ = v___y_1667_;
v___y_1691_ = v___y_1668_;
v___y_1692_ = v___y_1669_;
v___y_1693_ = v___y_1670_;
v___y_1694_ = v___y_1671_;
v___y_1695_ = v___y_1672_;
goto v___jp_1689_;
}
else
{
lean_dec(v_a_1688_);
lean_dec(v_a_1686_);
lean_dec(v_ctorSyntax_1663_);
lean_dec(v_levelParams_1662_);
lean_dec(v_name_1660_);
return v___x_1718_;
}
}
}
else
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1726_; 
lean_dec(v_a_1688_);
lean_dec(v_a_1686_);
lean_dec(v_ctorSyntax_1663_);
lean_dec(v_levelParams_1662_);
lean_dec(v_cls_1661_);
lean_dec(v_name_1660_);
v_a_1719_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1721_ = v___x_1712_;
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1712_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1726_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1724_; 
if (v_isShared_1722_ == 0)
{
v___x_1724_ = v___x_1721_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_a_1719_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
v___jp_1689_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1711_; 
v___x_1696_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1660_);
v___x_1697_ = lean_box(0);
lean_inc(v_a_1686_);
v___x_1698_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1696_, v_levelParams_1662_, v_a_1688_, v_a_1686_, v___x_1697_, v___y_1695_);
v_a_1699_ = lean_ctor_get(v___x_1698_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1701_ = v___x_1698_;
v_isShared_1702_ = v_isSharedCheck_1711_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1698_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1711_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
lean_ctor_set_tag(v___x_1701_, 1);
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_addDecl(v___x_1704_, v___x_1684_, v___y_1694_, v___y_1695_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; 
lean_dec_ref_known(v___x_1705_, 1);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_box(0);
v___x_1708_ = 1;
v___x_1709_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1663_, v_a_1686_, v___x_1706_, v___x_1706_, v___x_1707_, v___x_1708_, v___x_1684_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
return v___x_1709_;
}
else
{
lean_dec(v_a_1686_);
lean_dec(v_ctorSyntax_1663_);
return v___x_1705_;
}
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_dec(v_a_1686_);
lean_dec_ref(v___f_1664_);
lean_dec(v_ctorSyntax_1663_);
lean_dec(v_levelParams_1662_);
lean_dec(v_cls_1661_);
lean_dec(v_name_1660_);
v_a_1727_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1687_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1687_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v___f_1664_);
lean_dec(v_ctorSyntax_1663_);
lean_dec(v_levelParams_1662_);
lean_dec(v_cls_1661_);
lean_dec(v_name_1660_);
v_a_1735_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1685_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1685_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object** _args){
lean_object* v___x_1743_ = _args[0];
lean_object* v_numParams_1744_ = _args[1];
lean_object* v___x_1745_ = _args[2];
lean_object* v___x_1746_ = _args[3];
lean_object* v___x_1747_ = _args[4];
lean_object* v___x_1748_ = _args[5];
lean_object* v_name_1749_ = _args[6];
lean_object* v_name_1750_ = _args[7];
lean_object* v_cls_1751_ = _args[8];
lean_object* v_levelParams_1752_ = _args[9];
lean_object* v_ctorSyntax_1753_ = _args[10];
lean_object* v___f_1754_ = _args[11];
lean_object* v_args_1755_ = _args[12];
lean_object* v_body_1756_ = _args[13];
lean_object* v___y_1757_ = _args[14];
lean_object* v___y_1758_ = _args[15];
lean_object* v___y_1759_ = _args[16];
lean_object* v___y_1760_ = _args[17];
lean_object* v___y_1761_ = _args[18];
lean_object* v___y_1762_ = _args[19];
lean_object* v___y_1763_ = _args[20];
_start:
{
size_t v___x_8915__boxed_1764_; lean_object* v_res_1765_; 
v___x_8915__boxed_1764_ = lean_unbox_usize(v___x_1747_);
lean_dec(v___x_1747_);
v_res_1765_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1743_, v_numParams_1744_, v___x_1745_, v___x_1746_, v___x_8915__boxed_1764_, v___x_1748_, v_name_1749_, v_name_1750_, v_cls_1751_, v_levelParams_1752_, v_ctorSyntax_1753_, v___f_1754_, v_args_1755_, v_body_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec_ref(v_body_1756_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1766_, size_t v_i_1767_, lean_object* v_bs_1768_){
_start:
{
uint8_t v___x_1769_; 
v___x_1769_ = lean_usize_dec_lt(v_i_1767_, v_sz_1766_);
if (v___x_1769_ == 0)
{
return v_bs_1768_;
}
else
{
lean_object* v_v_1770_; lean_object* v_toConstantVal_1771_; lean_object* v_name_1772_; lean_object* v___x_1773_; lean_object* v_bs_x27_1774_; lean_object* v___x_1775_; size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v_v_1770_ = lean_array_uget_borrowed(v_bs_1768_, v_i_1767_);
v_toConstantVal_1771_ = lean_ctor_get(v_v_1770_, 0);
v_name_1772_ = lean_ctor_get(v_toConstantVal_1771_, 0);
lean_inc(v_name_1772_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v_bs_x27_1774_ = lean_array_uset(v_bs_1768_, v_i_1767_, v___x_1773_);
v___x_1775_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1772_);
v___x_1776_ = ((size_t)1ULL);
v___x_1777_ = lean_usize_add(v_i_1767_, v___x_1776_);
v___x_1778_ = lean_array_uset(v_bs_x27_1774_, v_i_1767_, v___x_1775_);
v_i_1767_ = v___x_1777_;
v_bs_1768_ = v___x_1778_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1780_, lean_object* v_i_1781_, lean_object* v_bs_1782_){
_start:
{
size_t v_sz_boxed_1783_; size_t v_i_boxed_1784_; lean_object* v_res_1785_; 
v_sz_boxed_1783_ = lean_unbox_usize(v_sz_1780_);
lean_dec(v_sz_1780_);
v_i_boxed_1784_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1783_, v_i_boxed_1784_, v_bs_1782_);
return v_res_1785_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2(void){
_start:
{
lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1));
v___x_1790_ = l_Lean_stringToMessageData(v___x_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1793_, lean_object* v_ctorSyntax_1794_, lean_object* v_numParams_1795_, lean_object* v_name_1796_, lean_object* v_ctor_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v_cls_1806_; lean_object* v___f_1807_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___x_1835_; lean_object* v_a_1836_; uint8_t v___x_1837_; 
v___x_1805_ = l_Lean_instInhabitedInductiveVal_default;
v_cls_1806_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___f_1807_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1835_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1806_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1835_);
v___x_1837_ = lean_unbox(v_a_1836_);
lean_dec(v_a_1836_);
if (v___x_1837_ == 0)
{
v___y_1809_ = v_a_1798_;
v___y_1810_ = v_a_1799_;
v___y_1811_ = v_a_1800_;
v___y_1812_ = v_a_1801_;
v___y_1813_ = v_a_1802_;
v___y_1814_ = v_a_1803_;
goto v___jp_1808_;
}
else
{
lean_object* v_toConstantVal_1838_; lean_object* v_name_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_toConstantVal_1838_ = lean_ctor_get(v_ctor_1797_, 0);
v_name_1839_ = lean_ctor_get(v_toConstantVal_1838_, 0);
v___x_1840_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
lean_inc(v_name_1839_);
v___x_1841_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1839_);
v___x_1842_ = l_Lean_MessageData_ofName(v___x_1841_);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1840_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1806_, v___x_1843_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_dec_ref_known(v___x_1844_, 1);
v___y_1809_ = v_a_1798_;
v___y_1810_ = v_a_1799_;
v___y_1811_ = v_a_1800_;
v___y_1812_ = v_a_1801_;
v___y_1813_ = v_a_1802_;
v___y_1814_ = v_a_1803_;
goto v___jp_1808_;
}
else
{
lean_dec_ref(v_ctor_1797_);
lean_dec(v_name_1796_);
lean_dec(v_numParams_1795_);
lean_dec(v_ctorSyntax_1794_);
lean_dec_ref(v_infos_1793_);
return v___x_1844_;
}
}
v___jp_1808_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v_toConstantVal_1817_; lean_object* v_toConstantVal_1818_; lean_object* v_levelParams_1819_; lean_object* v_name_1820_; lean_object* v_levelParams_1821_; lean_object* v_type_1822_; lean_object* v___x_1823_; size_t v_sz_1824_; size_t v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___f_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_borrowed(v___x_1805_, v_infos_1793_, v___x_1815_);
v_toConstantVal_1817_ = lean_ctor_get(v___x_1816_, 0);
v_toConstantVal_1818_ = lean_ctor_get(v_ctor_1797_, 0);
lean_inc_ref(v_toConstantVal_1818_);
lean_dec_ref(v_ctor_1797_);
v_levelParams_1819_ = lean_ctor_get(v_toConstantVal_1817_, 1);
lean_inc(v_levelParams_1819_);
v_name_1820_ = lean_ctor_get(v_toConstantVal_1818_, 0);
lean_inc(v_name_1820_);
v_levelParams_1821_ = lean_ctor_get(v_toConstantVal_1818_, 1);
lean_inc(v_levelParams_1821_);
v_type_1822_ = lean_ctor_get(v_toConstantVal_1818_, 2);
lean_inc_ref(v_type_1822_);
lean_dec_ref(v_toConstantVal_1818_);
v___x_1823_ = lean_array_get_size(v_infos_1793_);
v_sz_1824_ = lean_array_size(v_infos_1793_);
v___x_1825_ = ((size_t)0ULL);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1824_, v___x_1825_, v_infos_1793_);
v___x_1827_ = lean_box(0);
v___x_1828_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1819_, v___x_1827_);
v___x_1829_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1795_);
v___f_1830_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed), 21, 12);
lean_closure_set(v___f_1830_, 0, v___x_1815_);
lean_closure_set(v___f_1830_, 1, v_numParams_1795_);
lean_closure_set(v___f_1830_, 2, v___x_1826_);
lean_closure_set(v___f_1830_, 3, v___x_1828_);
lean_closure_set(v___f_1830_, 4, v___x_1829_);
lean_closure_set(v___f_1830_, 5, v___x_1823_);
lean_closure_set(v___f_1830_, 6, v_name_1796_);
lean_closure_set(v___f_1830_, 7, v_name_1820_);
lean_closure_set(v___f_1830_, 8, v_cls_1806_);
lean_closure_set(v___f_1830_, 9, v_levelParams_1821_);
lean_closure_set(v___f_1830_, 10, v_ctorSyntax_1794_);
lean_closure_set(v___f_1830_, 11, v___f_1807_);
v___x_1831_ = lean_nat_add(v_numParams_1795_, v___x_1823_);
lean_dec(v_numParams_1795_);
v___x_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
v___x_1833_ = 0;
v___x_1834_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1822_, v___x_1832_, v___f_1830_, v___x_1833_, v___x_1833_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
return v___x_1834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1845_, lean_object* v_ctorSyntax_1846_, lean_object* v_numParams_1847_, lean_object* v_name_1848_, lean_object* v_ctor_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1845_, v_ctorSyntax_1846_, v_numParams_1847_, v_name_1848_, v_ctor_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_mvarId_1858_, lean_object* v_val_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1858_, v_val_1859_, v___y_1863_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_mvarId_1868_, lean_object* v_val_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1868_, v_val_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_);
lean_dec(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_cls_1878_, lean_object* v_msg_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1878_, v_msg_1879_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_cls_1888_, lean_object* v_msg_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1888_, v_msg_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec_ref(v___y_1892_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
return v_res_1897_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_instMonadEIO___redArg();
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_toApplicative_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_2006_; 
v___x_1913_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1914_ = l_StateRefT_x27_instMonad___redArg(v___x_1913_);
v_toApplicative_1915_ = lean_ctor_get(v___x_1914_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; 
v_unused_2007_ = lean_ctor_get(v___x_1914_, 1);
lean_dec(v_unused_2007_);
v___x_1917_ = v___x_1914_;
v_isShared_1918_ = v_isSharedCheck_2006_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_toApplicative_1915_);
lean_dec(v___x_1914_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_2006_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v_toFunctor_1919_; lean_object* v_toSeq_1920_; lean_object* v_toSeqLeft_1921_; lean_object* v_toSeqRight_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_2004_; 
v_toFunctor_1919_ = lean_ctor_get(v_toApplicative_1915_, 0);
v_toSeq_1920_ = lean_ctor_get(v_toApplicative_1915_, 2);
v_toSeqLeft_1921_ = lean_ctor_get(v_toApplicative_1915_, 3);
v_toSeqRight_1922_ = lean_ctor_get(v_toApplicative_1915_, 4);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_toApplicative_1915_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v_toApplicative_1915_, 1);
lean_dec(v_unused_2005_);
v___x_1924_ = v_toApplicative_1915_;
v_isShared_1925_ = v_isSharedCheck_2004_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_toSeqRight_1922_);
lean_inc(v_toSeqLeft_1921_);
lean_inc(v_toSeq_1920_);
lean_inc(v_toFunctor_1919_);
lean_dec(v_toApplicative_1915_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_2004_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___f_1926_; lean_object* v___f_1927_; lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___x_1930_; lean_object* v___f_1931_; lean_object* v___f_1932_; lean_object* v___f_1933_; lean_object* v___x_1935_; 
v___f_1926_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1927_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1919_);
v___f_1928_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1928_, 0, v_toFunctor_1919_);
v___f_1929_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1929_, 0, v_toFunctor_1919_);
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___f_1928_);
lean_ctor_set(v___x_1930_, 1, v___f_1929_);
v___f_1931_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1931_, 0, v_toSeqRight_1922_);
v___f_1932_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1932_, 0, v_toSeqLeft_1921_);
v___f_1933_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1933_, 0, v_toSeq_1920_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 4, v___f_1931_);
lean_ctor_set(v___x_1924_, 3, v___f_1932_);
lean_ctor_set(v___x_1924_, 2, v___f_1933_);
lean_ctor_set(v___x_1924_, 1, v___f_1926_);
lean_ctor_set(v___x_1924_, 0, v___x_1930_);
v___x_1935_ = v___x_1924_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___f_1926_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v___f_1933_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v___f_1932_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v___f_1931_);
v___x_1935_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1937_; 
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v___f_1927_);
lean_ctor_set(v___x_1917_, 0, v___x_1935_);
v___x_1937_ = v___x_1917_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1935_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___f_1927_);
v___x_1937_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v_toApplicative_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_2000_; 
v___x_1938_ = l_StateRefT_x27_instMonad___redArg(v___x_1937_);
v_toApplicative_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v___x_1938_, 1);
lean_dec(v_unused_2001_);
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_2000_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_toApplicative_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_2000_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v_toFunctor_1943_; lean_object* v_toSeq_1944_; lean_object* v_toSeqLeft_1945_; lean_object* v_toSeqRight_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1998_; 
v_toFunctor_1943_ = lean_ctor_get(v_toApplicative_1939_, 0);
v_toSeq_1944_ = lean_ctor_get(v_toApplicative_1939_, 2);
v_toSeqLeft_1945_ = lean_ctor_get(v_toApplicative_1939_, 3);
v_toSeqRight_1946_ = lean_ctor_get(v_toApplicative_1939_, 4);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_toApplicative_1939_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v_toApplicative_1939_, 1);
lean_dec(v_unused_1999_);
v___x_1948_ = v_toApplicative_1939_;
v_isShared_1949_ = v_isSharedCheck_1998_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_toSeqRight_1946_);
lean_inc(v_toSeqLeft_1945_);
lean_inc(v_toSeq_1944_);
lean_inc(v_toFunctor_1943_);
lean_dec(v_toApplicative_1939_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1998_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___x_1954_; lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v___f_1957_; lean_object* v___x_1959_; 
v___f_1950_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1951_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1943_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toFunctor_1943_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toFunctor_1943_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___f_1952_);
lean_ctor_set(v___x_1954_, 1, v___f_1953_);
v___f_1955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1955_, 0, v_toSeqRight_1946_);
v___f_1956_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1956_, 0, v_toSeqLeft_1945_);
v___f_1957_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1957_, 0, v_toSeq_1944_);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 4, v___f_1955_);
lean_ctor_set(v___x_1948_, 3, v___f_1956_);
lean_ctor_set(v___x_1948_, 2, v___f_1957_);
lean_ctor_set(v___x_1948_, 1, v___f_1950_);
lean_ctor_set(v___x_1948_, 0, v___x_1954_);
v___x_1959_ = v___x_1948_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___f_1950_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v___f_1957_);
lean_ctor_set(v_reuseFailAlloc_1997_, 3, v___f_1956_);
lean_ctor_set(v_reuseFailAlloc_1997_, 4, v___f_1955_);
v___x_1959_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 1, v___f_1951_);
lean_ctor_set(v___x_1941_, 0, v___x_1959_);
v___x_1961_ = v___x_1941_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1959_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___f_1951_);
v___x_1961_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v_toApplicative_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1994_; 
v___x_1962_ = l_StateRefT_x27_instMonad___redArg(v___x_1961_);
v_toApplicative_1963_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v___x_1962_, 1);
lean_dec(v_unused_1995_);
v___x_1965_ = v___x_1962_;
v_isShared_1966_ = v_isSharedCheck_1994_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_toApplicative_1963_);
lean_dec(v___x_1962_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1994_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_toFunctor_1967_; lean_object* v_toSeq_1968_; lean_object* v_toSeqLeft_1969_; lean_object* v_toSeqRight_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1992_; 
v_toFunctor_1967_ = lean_ctor_get(v_toApplicative_1963_, 0);
v_toSeq_1968_ = lean_ctor_get(v_toApplicative_1963_, 2);
v_toSeqLeft_1969_ = lean_ctor_get(v_toApplicative_1963_, 3);
v_toSeqRight_1970_ = lean_ctor_get(v_toApplicative_1963_, 4);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_toApplicative_1963_);
if (v_isSharedCheck_1992_ == 0)
{
lean_object* v_unused_1993_; 
v_unused_1993_ = lean_ctor_get(v_toApplicative_1963_, 1);
lean_dec(v_unused_1993_);
v___x_1972_ = v_toApplicative_1963_;
v_isShared_1973_ = v_isSharedCheck_1992_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_toSeqRight_1970_);
lean_inc(v_toSeqLeft_1969_);
lean_inc(v_toSeq_1968_);
lean_inc(v_toFunctor_1967_);
lean_dec(v_toApplicative_1963_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1992_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___x_1978_; lean_object* v___f_1979_; lean_object* v___f_1980_; lean_object* v___f_1981_; lean_object* v___x_1983_; 
v___f_1974_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_1975_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1967_);
v___f_1976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1976_, 0, v_toFunctor_1967_);
v___f_1977_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1977_, 0, v_toFunctor_1967_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___f_1976_);
lean_ctor_set(v___x_1978_, 1, v___f_1977_);
v___f_1979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1979_, 0, v_toSeqRight_1970_);
v___f_1980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1980_, 0, v_toSeqLeft_1969_);
v___f_1981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1981_, 0, v_toSeq_1968_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 4, v___f_1979_);
lean_ctor_set(v___x_1972_, 3, v___f_1980_);
lean_ctor_set(v___x_1972_, 2, v___f_1981_);
lean_ctor_set(v___x_1972_, 1, v___f_1974_);
lean_ctor_set(v___x_1972_, 0, v___x_1978_);
v___x_1983_ = v___x_1972_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___f_1974_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v___f_1981_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v___f_1980_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v___f_1979_);
v___x_1983_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v___x_1985_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 1, v___f_1975_);
lean_ctor_set(v___x_1965_, 0, v___x_1983_);
v___x_1985_ = v___x_1965_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1983_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___f_1975_);
v___x_1985_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_3785__overap_1988_; lean_object* v___x_1989_; 
v___x_1986_ = lean_box(0);
v___x_1987_ = l_instInhabitedOfMonad___redArg(v___x_1985_, v___x_1986_);
v___x_3785__overap_1988_ = lean_panic_fn_borrowed(v___x_1987_, v_msg_1905_);
lean_dec(v___x_1987_);
lean_inc(v___y_1911_);
lean_inc_ref(v___y_1910_);
lean_inc(v___y_1909_);
lean_inc_ref(v___y_1908_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
v___x_1989_ = lean_apply_7(v___x_3785__overap_1988_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, lean_box(0));
return v___x_1989_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2016_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2017_, lean_object* v_opt_2018_){
_start:
{
lean_object* v_name_2019_; lean_object* v_defValue_2020_; lean_object* v_map_2021_; lean_object* v___x_2022_; 
v_name_2019_ = lean_ctor_get(v_opt_2018_, 0);
v_defValue_2020_ = lean_ctor_get(v_opt_2018_, 1);
v_map_2021_ = lean_ctor_get(v_opts_2017_, 0);
v___x_2022_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2021_, v_name_2019_);
if (lean_obj_tag(v___x_2022_) == 0)
{
uint8_t v___x_2023_; 
v___x_2023_ = lean_unbox(v_defValue_2020_);
return v___x_2023_;
}
else
{
lean_object* v_val_2024_; 
v_val_2024_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_val_2024_);
lean_dec_ref_known(v___x_2022_, 1);
if (lean_obj_tag(v_val_2024_) == 1)
{
uint8_t v_v_2025_; 
v_v_2025_ = lean_ctor_get_uint8(v_val_2024_, 0);
lean_dec_ref_known(v_val_2024_, 0);
return v_v_2025_;
}
else
{
uint8_t v___x_2026_; 
lean_dec(v_val_2024_);
v___x_2026_ = lean_unbox(v_defValue_2020_);
return v___x_2026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2027_, lean_object* v_opt_2028_){
_start:
{
uint8_t v_res_2029_; lean_object* v_r_2030_; 
v_res_2029_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2027_, v_opt_2028_);
lean_dec_ref(v_opt_2028_);
lean_dec_ref(v_opts_2027_);
v_r_2030_ = lean_box(v_res_2029_);
return v_r_2030_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = lean_box(1);
v___x_2032_ = l_Lean_MessageData_ofFormat(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2037_ = l_Lean_MessageData_ofFormat(v___x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2038_, lean_object* v_x_2039_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 0)
{
return v_x_2038_;
}
else
{
lean_object* v_head_2040_; lean_object* v_tail_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2063_; 
v_head_2040_ = lean_ctor_get(v_x_2039_, 0);
v_tail_2041_ = lean_ctor_get(v_x_2039_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_x_2039_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2043_ = v_x_2039_;
v_isShared_2044_ = v_isSharedCheck_2063_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_tail_2041_);
lean_inc(v_head_2040_);
lean_dec(v_x_2039_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2063_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_before_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2061_; 
v_before_2045_ = lean_ctor_get(v_head_2040_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_head_2040_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_head_2040_, 1);
lean_dec(v_unused_2062_);
v___x_2047_ = v_head_2040_;
v_isShared_2048_ = v_isSharedCheck_2061_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_before_2045_);
lean_dec(v_head_2040_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2061_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2048_ == 0)
{
lean_ctor_set_tag(v___x_2047_, 7);
lean_ctor_set(v___x_2047_, 1, v___x_2049_);
lean_ctor_set(v___x_2047_, 0, v_x_2038_);
v___x_2051_ = v___x_2047_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_x_2038_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2052_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 7);
lean_ctor_set(v___x_2043_, 1, v___x_2052_);
lean_ctor_set(v___x_2043_, 0, v___x_2051_);
v___x_2054_ = v___x_2043_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2055_ = l_Lean_MessageData_ofSyntax(v_before_2045_);
v___x_2056_ = l_Lean_indentD(v___x_2055_);
v___x_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2054_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v_x_2038_ = v___x_2057_;
v_x_2039_ = v_tail_2041_;
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
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2068_ = l_Lean_MessageData_ofFormat(v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2069_, lean_object* v_macroStack_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2073_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2071_);
v___x_2074_ = l_Lean_Elab_pp_macroStack;
v___x_2075_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v___x_2073_, v___x_2074_);
lean_dec_ref(v___x_2073_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
lean_dec(v_macroStack_2070_);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_msgData_2069_);
return v___x_2076_;
}
else
{
if (lean_obj_tag(v_macroStack_2070_) == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_msgData_2069_);
return v___x_2077_;
}
else
{
lean_object* v_head_2078_; lean_object* v_after_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2094_; 
v_head_2078_ = lean_ctor_get(v_macroStack_2070_, 0);
lean_inc(v_head_2078_);
v_after_2079_ = lean_ctor_get(v_head_2078_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_head_2078_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v_head_2078_, 0);
lean_dec(v_unused_2095_);
v___x_2081_ = v_head_2078_;
v_isShared_2082_ = v_isSharedCheck_2094_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_after_2079_);
lean_dec(v_head_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2094_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2082_ == 0)
{
lean_ctor_set_tag(v___x_2081_, 7);
lean_ctor_set(v___x_2081_, 1, v___x_2083_);
lean_ctor_set(v___x_2081_, 0, v_msgData_2069_);
v___x_2085_ = v___x_2081_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_msgData_2069_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v_msgData_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2086_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2085_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = l_Lean_MessageData_ofSyntax(v_after_2079_);
v___x_2089_ = l_Lean_indentD(v___x_2088_);
v_msgData_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2090_, 0, v___x_2087_);
lean_ctor_set(v_msgData_2090_, 1, v___x_2089_);
v___x_2091_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2090_, v_macroStack_2070_);
v___x_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
return v___x_2092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2096_, lean_object* v_macroStack_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2096_, v_macroStack_2097_, v___y_2098_);
lean_dec_ref(v___y_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_ref_2109_; lean_object* v_macroStack_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_a_2113_; lean_object* v___x_2114_; lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
v_ref_2109_ = lean_ctor_get(v___y_2106_, 2);
v_macroStack_2110_ = lean_ctor_get(v___y_2102_, 1);
v___x_2111_ = l_Lean_Elab_getBetterRef(v_ref_2109_, v_macroStack_2110_);
v___x_2112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2101_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___x_2112_);
lean_inc(v_macroStack_2110_);
v___x_2114_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2113_, v_macroStack_2110_, v___y_2106_);
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2117_ = v___x_2114_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2114_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2111_);
lean_ctor_set(v___x_2119_, 1, v_a_2115_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set_tag(v___x_2117_, 1);
lean_ctor_set(v___x_2117_, 0, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2132_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2142_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2143_ = lean_unsigned_to_nat(11u);
v___x_2144_ = lean_unsigned_to_nat(122u);
v___x_2145_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2146_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2147_ = l_mkPanicMessageWithDecl(v___x_2146_, v___x_2145_, v___x_2144_, v___x_2143_, v___x_2142_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2164_; lean_object* v_env_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; 
v___x_2164_ = lean_st_ref_get(v___y_2154_);
v_env_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc_ref(v_env_2165_);
lean_dec(v___x_2164_);
v___x_2166_ = 0;
lean_inc(v_constName_2148_);
v___x_2167_ = l_Lean_Environment_findAsync_x3f(v_env_2165_, v_constName_2148_, v___x_2166_);
if (lean_obj_tag(v___x_2167_) == 1)
{
lean_object* v_val_2168_; uint8_t v_kind_2169_; 
v_val_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_val_2168_);
lean_dec_ref_known(v___x_2167_, 1);
v_kind_2169_ = lean_ctor_get_uint8(v_val_2168_, sizeof(void*)*3);
if (v_kind_2169_ == 6)
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2168_);
if (lean_obj_tag(v___x_2170_) == 6)
{
lean_object* v_val_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_constName_2148_);
v_val_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_val_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set_tag(v___x_2173_, 0);
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_val_2171_);
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
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec_ref(v___x_2170_);
v___x_2179_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2180_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2179_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2189_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2189_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2189_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
if (lean_obj_tag(v_a_2181_) == 0)
{
lean_del_object(v___x_2183_);
goto v___jp_2156_;
}
else
{
lean_object* v_val_2185_; lean_object* v___x_2187_; 
lean_dec(v_constName_2148_);
v_val_2185_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_val_2185_);
lean_dec_ref_known(v_a_2181_, 1);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v_val_2185_);
v___x_2187_ = v___x_2183_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_val_2185_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_constName_2148_);
v_a_2190_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2180_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2180_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
else
{
lean_dec(v_val_2168_);
goto v___jp_2156_;
}
}
else
{
lean_dec(v___x_2167_);
goto v___jp_2156_;
}
v___jp_2156_:
{
lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2157_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2158_ = 0;
v___x_2159_ = l_Lean_MessageData_ofConstName(v_constName_2148_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2162_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2207_, lean_object* v_infos_2208_, lean_object* v_numParams_2209_, lean_object* v_as_x27_2210_, lean_object* v_b_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
if (lean_obj_tag(v_as_x27_2210_) == 0)
{
lean_object* v___x_2219_; 
lean_dec(v_numParams_2209_);
lean_dec_ref(v_infos_2208_);
lean_dec_ref(v_a_2207_);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_b_2211_);
return v___x_2219_;
}
else
{
lean_object* v_head_2220_; lean_object* v_tail_2221_; lean_object* v_array_2222_; lean_object* v_start_2223_; lean_object* v_stop_2224_; uint8_t v___x_2225_; 
v_head_2220_ = lean_ctor_get(v_as_x27_2210_, 0);
v_tail_2221_ = lean_ctor_get(v_as_x27_2210_, 1);
v_array_2222_ = lean_ctor_get(v_b_2211_, 0);
v_start_2223_ = lean_ctor_get(v_b_2211_, 1);
v_stop_2224_ = lean_ctor_get(v_b_2211_, 2);
v___x_2225_ = lean_nat_dec_lt(v_start_2223_, v_stop_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
lean_dec(v_numParams_2209_);
lean_dec_ref(v_infos_2208_);
lean_dec_ref(v_a_2207_);
v___x_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_b_2211_);
return v___x_2226_;
}
else
{
lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2258_; 
lean_inc(v_stop_2224_);
lean_inc(v_start_2223_);
lean_inc_ref(v_array_2222_);
v_isSharedCheck_2258_ = !lean_is_exclusive(v_b_2211_);
if (v_isSharedCheck_2258_ == 0)
{
lean_object* v_unused_2259_; lean_object* v_unused_2260_; lean_object* v_unused_2261_; 
v_unused_2259_ = lean_ctor_get(v_b_2211_, 2);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_b_2211_, 1);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_b_2211_, 0);
lean_dec(v_unused_2261_);
v___x_2228_ = v_b_2211_;
v_isShared_2229_ = v_isSharedCheck_2258_;
goto v_resetjp_2227_;
}
else
{
lean_dec(v_b_2211_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2258_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2230_ = lean_array_fget(v_array_2222_, v_start_2223_);
v___x_2231_ = lean_unsigned_to_nat(1u);
v___x_2232_ = lean_nat_add(v_start_2223_, v___x_2231_);
lean_dec(v_start_2223_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set(v___x_2228_, 1, v___x_2232_);
v___x_2234_ = v___x_2228_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_array_2222_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_stop_2224_);
v___x_2234_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
lean_object* v___x_2235_; 
lean_inc(v_head_2220_);
v___x_2235_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2220_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_toConstantVal_2236_; lean_object* v_a_2237_; lean_object* v_name_2238_; lean_object* v___x_2239_; 
v_toConstantVal_2236_ = lean_ctor_get(v_a_2207_, 0);
v_a_2237_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2237_);
lean_dec_ref_known(v___x_2235_, 1);
v_name_2238_ = lean_ctor_get(v_toConstantVal_2236_, 0);
lean_inc(v_name_2238_);
lean_inc(v_numParams_2209_);
lean_inc_ref(v_infos_2208_);
v___x_2239_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2208_, v___x_2230_, v_numParams_2209_, v_name_2238_, v_a_2237_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_dec_ref_known(v___x_2239_, 1);
v_as_x27_2210_ = v_tail_2221_;
v_b_2211_ = v___x_2234_;
goto _start;
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_dec_ref(v___x_2234_);
lean_dec(v_numParams_2209_);
lean_dec_ref(v_infos_2208_);
lean_dec_ref(v_a_2207_);
v_a_2241_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2239_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2239_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v___x_2234_);
lean_dec(v___x_2230_);
lean_dec(v_numParams_2209_);
lean_dec_ref(v_infos_2208_);
lean_dec_ref(v_a_2207_);
v_a_2249_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2235_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2235_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2262_, lean_object* v_infos_2263_, lean_object* v_numParams_2264_, lean_object* v_as_x27_2265_, lean_object* v_b_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2262_, v_infos_2263_, v_numParams_2264_, v_as_x27_2265_, v_b_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v_as_x27_2265_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2275_, lean_object* v_numParams_2276_, lean_object* v_as_2277_, size_t v_sz_2278_, size_t v_i_2279_, lean_object* v_b_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
uint8_t v___x_2288_; 
v___x_2288_ = lean_usize_dec_lt(v_i_2279_, v_sz_2278_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_dec(v_numParams_2276_);
lean_dec_ref(v_infos_2275_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_b_2280_);
return v___x_2289_;
}
else
{
lean_object* v_array_2290_; lean_object* v_start_2291_; lean_object* v_stop_2292_; uint8_t v___x_2293_; 
v_array_2290_ = lean_ctor_get(v_b_2280_, 0);
v_start_2291_ = lean_ctor_get(v_b_2280_, 1);
v_stop_2292_ = lean_ctor_get(v_b_2280_, 2);
v___x_2293_ = lean_nat_dec_lt(v_start_2291_, v_stop_2292_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; 
lean_dec(v_numParams_2276_);
lean_dec_ref(v_infos_2275_);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v_b_2280_);
return v___x_2294_;
}
else
{
lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2322_; 
lean_inc(v_stop_2292_);
lean_inc(v_start_2291_);
lean_inc_ref(v_array_2290_);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_b_2280_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; lean_object* v_unused_2324_; lean_object* v_unused_2325_; 
v_unused_2323_ = lean_ctor_get(v_b_2280_, 2);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_b_2280_, 1);
lean_dec(v_unused_2324_);
v_unused_2325_ = lean_ctor_get(v_b_2280_, 0);
lean_dec(v_unused_2325_);
v___x_2296_ = v_b_2280_;
v_isShared_2297_ = v_isSharedCheck_2322_;
goto v_resetjp_2295_;
}
else
{
lean_dec(v_b_2280_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2322_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v_ctorSyntax_2299_; lean_object* v_a_2300_; lean_object* v_ctors_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2298_ = lean_array_fget_borrowed(v_array_2290_, v_start_2291_);
v_ctorSyntax_2299_ = lean_ctor_get(v___x_2298_, 4);
lean_inc_ref(v_ctorSyntax_2299_);
v_a_2300_ = lean_array_uget_borrowed(v_as_2277_, v_i_2279_);
v_ctors_2301_ = lean_ctor_get(v_a_2300_, 4);
v___x_2302_ = lean_array_get_size(v_ctorSyntax_2299_);
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_nat_add(v_start_2291_, v___x_2303_);
lean_dec(v_start_2291_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2304_);
v___x_2306_ = v___x_2296_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_array_2290_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_stop_2292_);
v___x_2306_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_unsigned_to_nat(0u);
v___x_2308_ = l_Array_toSubarray___redArg(v_ctorSyntax_2299_, v___x_2307_, v___x_2302_);
lean_inc(v_numParams_2276_);
lean_inc_ref(v_infos_2275_);
lean_inc(v_a_2300_);
v___x_2309_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2300_, v_infos_2275_, v_numParams_2276_, v_ctors_2301_, v___x_2308_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2309_) == 0)
{
size_t v___x_2310_; size_t v___x_2311_; 
lean_dec_ref_known(v___x_2309_, 1);
v___x_2310_ = ((size_t)1ULL);
v___x_2311_ = lean_usize_add(v_i_2279_, v___x_2310_);
v_i_2279_ = v___x_2311_;
v_b_2280_ = v___x_2306_;
goto _start;
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec_ref(v___x_2306_);
lean_dec(v_numParams_2276_);
lean_dec_ref(v_infos_2275_);
v_a_2313_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2309_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2309_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2326_, lean_object* v_numParams_2327_, lean_object* v_as_2328_, lean_object* v_sz_2329_, lean_object* v_i_2330_, lean_object* v_b_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
size_t v_sz_boxed_2339_; size_t v_i_boxed_2340_; lean_object* v_res_2341_; 
v_sz_boxed_2339_ = lean_unbox_usize(v_sz_2329_);
lean_dec(v_sz_2329_);
v_i_boxed_2340_ = lean_unbox_usize(v_i_2330_);
lean_dec(v_i_2330_);
v_res_2341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2326_, v_numParams_2327_, v_as_2328_, v_sz_boxed_2339_, v_i_boxed_2340_, v_b_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec_ref(v_as_2328_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2342_, lean_object* v_infos_2343_, lean_object* v_coinductiveElabData_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; size_t v_sz_2355_; size_t v___x_2356_; lean_object* v___x_2357_; 
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_array_get_size(v_coinductiveElabData_2344_);
v___x_2354_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2344_, v___x_2352_, v___x_2353_);
v_sz_2355_ = lean_array_size(v_infos_2343_);
v___x_2356_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2343_);
v___x_2357_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2343_, v_numParams_2342_, v_infos_2343_, v_sz_2355_, v___x_2356_, v___x_2354_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec_ref(v_infos_2343_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2365_; 
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v___x_2357_, 0);
lean_dec(v_unused_2366_);
v___x_2359_ = v___x_2357_;
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
else
{
lean_dec(v___x_2357_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = lean_box(0);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2361_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_a_2367_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2357_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2357_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2375_, lean_object* v_infos_2376_, lean_object* v_coinductiveElabData_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2375_, v_infos_2376_, v_coinductiveElabData_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2386_, lean_object* v_infos_2387_, lean_object* v_numParams_2388_, lean_object* v_as_2389_, lean_object* v_as_x27_2390_, lean_object* v_b_2391_, lean_object* v_a_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2386_, v_infos_2387_, v_numParams_2388_, v_as_x27_2390_, v_b_2391_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2401_, lean_object* v_infos_2402_, lean_object* v_numParams_2403_, lean_object* v_as_2404_, lean_object* v_as_x27_2405_, lean_object* v_b_2406_, lean_object* v_a_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2401_, v_infos_2402_, v_numParams_2403_, v_as_2404_, v_as_x27_2405_, v_b_2406_, v_a_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v_as_x27_2405_);
lean_dec(v_as_2404_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2416_, lean_object* v_msg_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2426_, lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2426_, v_msg_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2436_, lean_object* v_macroStack_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2436_, v_macroStack_2437_, v___y_2442_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2446_, lean_object* v_macroStack_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2446_, v_macroStack_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_mvarId_2456_, lean_object* v_x_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v___x_2463_; 
v___x_2463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2456_, v_x_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2463_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2463_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_a_2472_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2463_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2463_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_mvarId_2480_, lean_object* v_x_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2480_, v_x_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2488_, lean_object* v_mvarId_2489_, lean_object* v_x_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2489_, v_x_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2497_, lean_object* v_mvarId_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2497_, v_mvarId_2498_, v_x_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_type_2506_, lean_object* v_maxFVars_x3f_2507_, lean_object* v_k_2508_, uint8_t v_cleanupAnnotations_2509_, uint8_t v_whnfType_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___f_2516_; lean_object* v___x_2517_; 
v___f_2516_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2516_, 0, v_k_2508_);
v___x_2517_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2506_, v_maxFVars_x3f_2507_, v___f_2516_, v_cleanupAnnotations_2509_, v_whnfType_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2523_; 
if (v_isShared_2521_ == 0)
{
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2517_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2517_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_type_2534_, lean_object* v_maxFVars_x3f_2535_, lean_object* v_k_2536_, lean_object* v_cleanupAnnotations_2537_, lean_object* v_whnfType_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2544_; uint8_t v_whnfType_boxed_2545_; lean_object* v_res_2546_; 
v_cleanupAnnotations_boxed_2544_ = lean_unbox(v_cleanupAnnotations_2537_);
v_whnfType_boxed_2545_ = lean_unbox(v_whnfType_2538_);
v_res_2546_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2534_, v_maxFVars_x3f_2535_, v_k_2536_, v_cleanupAnnotations_boxed_2544_, v_whnfType_boxed_2545_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2547_, lean_object* v_type_2548_, lean_object* v_maxFVars_x3f_2549_, lean_object* v_k_2550_, uint8_t v_cleanupAnnotations_2551_, uint8_t v_whnfType_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2548_, v_maxFVars_x3f_2549_, v_k_2550_, v_cleanupAnnotations_2551_, v_whnfType_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_type_2560_, lean_object* v_maxFVars_x3f_2561_, lean_object* v_k_2562_, lean_object* v_cleanupAnnotations_2563_, lean_object* v_whnfType_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2570_; uint8_t v_whnfType_boxed_2571_; lean_object* v_res_2572_; 
v_cleanupAnnotations_boxed_2570_ = lean_unbox(v_cleanupAnnotations_2563_);
v_whnfType_boxed_2571_ = lean_unbox(v_whnfType_2564_);
v_res_2572_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2559_, v_type_2560_, v_maxFVars_x3f_2561_, v_k_2562_, v_cleanupAnnotations_boxed_2570_, v_whnfType_boxed_2571_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2573_, lean_object* v_msg_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v_toCold_2580_; lean_object* v_currRecDepth_2581_; lean_object* v_ref_2582_; uint16_t v_optionFlags_2583_; uint8_t v_suppressElabErrors_2584_; uint8_t v_isRecordingDeps_2585_; lean_object* v_ref_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_toCold_2580_ = lean_ctor_get(v___y_2577_, 0);
v_currRecDepth_2581_ = lean_ctor_get(v___y_2577_, 1);
v_ref_2582_ = lean_ctor_get(v___y_2577_, 2);
v_optionFlags_2583_ = lean_ctor_get_uint16(v___y_2577_, sizeof(void*)*3);
v_suppressElabErrors_2584_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2585_ = lean_ctor_get_uint8(v___y_2577_, sizeof(void*)*3 + 3);
v_ref_2586_ = l_Lean_replaceRef(v_ref_2573_, v_ref_2582_);
lean_inc(v_currRecDepth_2581_);
lean_inc_ref(v_toCold_2580_);
v___x_2587_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2587_, 0, v_toCold_2580_);
lean_ctor_set(v___x_2587_, 1, v_currRecDepth_2581_);
lean_ctor_set(v___x_2587_, 2, v_ref_2586_);
lean_ctor_set_uint16(v___x_2587_, sizeof(void*)*3, v_optionFlags_2583_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*3 + 2, v_suppressElabErrors_2584_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*3 + 3, v_isRecordingDeps_2585_);
v___x_2588_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2574_, v___y_2575_, v___y_2576_, v___x_2587_, v___y_2578_);
lean_dec_ref_known(v___x_2587_, 3);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2589_, lean_object* v_msg_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2589_, v_msg_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v_ref_2589_);
return v_res_2596_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2597_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2600_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2601_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2602_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
lean_ctor_set(v___x_2603_, 2, v___x_2602_);
lean_ctor_set(v___x_2603_, 3, v___x_2602_);
lean_ctor_set(v___x_2603_, 4, v___x_2601_);
lean_ctor_set(v___x_2603_, 5, v___x_2601_);
lean_ctor_set(v___x_2603_, 6, v___x_2601_);
lean_ctor_set(v___x_2603_, 7, v___x_2601_);
lean_ctor_set(v___x_2603_, 8, v___x_2601_);
lean_ctor_set(v___x_2603_, 9, v___x_2601_);
lean_ctor_set(v___x_2603_, 10, v___x_2601_);
lean_ctor_set(v___x_2603_, 11, v___x_2600_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = lean_unsigned_to_nat(32u);
v___x_2605_ = lean_mk_empty_array_with_capacity(v___x_2604_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2607_ = ((size_t)5ULL);
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = lean_unsigned_to_nat(32u);
v___x_2610_ = lean_mk_empty_array_with_capacity(v___x_2609_);
v___x_2611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2612_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2610_);
lean_ctor_set(v___x_2612_, 2, v___x_2608_);
lean_ctor_set(v___x_2612_, 3, v___x_2608_);
lean_ctor_set_usize(v___x_2612_, 4, v___x_2607_);
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2613_ = lean_box(1);
v___x_2614_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2616_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2614_);
lean_ctor_set(v___x_2616_, 2, v___x_2613_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2619_ = l_Lean_stringToMessageData(v___x_2618_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2622_ = l_Lean_stringToMessageData(v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2631_ = l_Lean_stringToMessageData(v___x_2630_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2634_ = l_Lean_stringToMessageData(v___x_2633_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2637_ = l_Lean_stringToMessageData(v___x_2636_);
return v___x_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2638_, lean_object* v_declHint_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v_env_2644_; uint8_t v___x_2645_; 
v___x_2642_ = lean_box(0);
v___x_2643_ = lean_st_ref_get(v___y_2640_);
v_env_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc_ref(v_env_2644_);
lean_dec(v___x_2643_);
v___x_2645_ = l_Lean_Name_isAnonymous(v_declHint_2639_);
if (v___x_2645_ == 0)
{
uint8_t v_isExporting_2646_; 
v_isExporting_2646_ = lean_ctor_get_uint8(v_env_2644_, sizeof(void*)*13);
if (v_isExporting_2646_ == 0)
{
lean_object* v___x_2647_; 
lean_dec_ref(v_env_2644_);
lean_dec(v_declHint_2639_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v_msg_2638_);
return v___x_2647_;
}
else
{
lean_object* v___x_2648_; uint8_t v___x_2649_; 
lean_inc_ref(v_env_2644_);
v___x_2648_ = l_Lean_Environment_setExporting(v_env_2644_, v___x_2645_);
lean_inc(v_declHint_2639_);
lean_inc_ref(v___x_2648_);
v___x_2649_ = l_Lean_Environment_contains(v___x_2648_, v_declHint_2639_, v_isExporting_2646_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref(v___x_2648_);
lean_dec_ref(v_env_2644_);
lean_dec(v_declHint_2639_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_msg_2638_);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v_c_2656_; lean_object* v___x_2657_; 
v___x_2651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2652_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2653_ = l_Lean_Options_empty;
v___x_2654_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2648_);
lean_ctor_set(v___x_2654_, 1, v___x_2651_);
lean_ctor_set(v___x_2654_, 2, v___x_2652_);
lean_ctor_set(v___x_2654_, 3, v___x_2653_);
lean_inc(v_declHint_2639_);
v___x_2655_ = l_Lean_MessageData_ofConstName(v_declHint_2639_, v___x_2645_);
v_c_2656_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2656_, 0, v___x_2654_);
lean_ctor_set(v_c_2656_, 1, v___x_2655_);
v___x_2657_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2644_, v_declHint_2639_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_dec_ref(v_env_2644_);
lean_dec(v_declHint_2639_);
v___x_2658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v_c_2656_);
v___x_2660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2659_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_MessageData_note(v___x_2661_);
v___x_2663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_msg_2638_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
return v___x_2664_;
}
else
{
lean_object* v_val_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2699_; 
v_val_2665_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2667_ = v___x_2657_;
v_isShared_2668_ = v_isSharedCheck_2699_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_val_2665_);
lean_dec(v___x_2657_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2699_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v_moduleNames_2670_; lean_object* v_mod_2671_; uint8_t v___x_2672_; 
v___x_2669_ = l_Lean_Environment_header(v_env_2644_);
lean_dec_ref(v_env_2644_);
v_moduleNames_2670_ = lean_ctor_get(v___x_2669_, 4);
lean_inc_ref(v_moduleNames_2670_);
lean_dec_ref(v___x_2669_);
v_mod_2671_ = lean_array_get(v___x_2642_, v_moduleNames_2670_, v_val_2665_);
lean_dec(v_val_2665_);
lean_dec_ref(v_moduleNames_2670_);
v___x_2672_ = l_Lean_isPrivateName(v_declHint_2639_);
lean_dec(v_declHint_2639_);
if (v___x_2672_ == 0)
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
lean_ctor_set(v___x_2674_, 1, v_c_2656_);
v___x_2675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_MessageData_ofName(v_mod_2671_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2676_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_MessageData_note(v___x_2680_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v_msg_2638_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set_tag(v___x_2667_, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2682_);
v___x_2684_ = v___x_2667_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
lean_ctor_set(v___x_2687_, 1, v_c_2656_);
v___x_2688_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = l_Lean_MessageData_ofName(v_mod_2671_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2689_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_Lean_MessageData_note(v___x_2693_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v_msg_2638_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set_tag(v___x_2667_, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2695_);
v___x_2697_ = v___x_2667_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2700_; 
lean_dec_ref(v_env_2644_);
lean_dec(v_declHint_2639_);
v___x_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_msg_2638_);
return v___x_2700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2701_, lean_object* v_declHint_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2701_, v_declHint_2702_, v___y_2703_);
lean_dec(v___y_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2706_, lean_object* v_declHint_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2723_; 
v___x_2713_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2706_, v_declHint_2707_, v___y_2711_);
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2723_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2723_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2721_; 
v___x_2718_ = l_Lean_unknownIdentifierMessageTag;
v___x_2719_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2719_, 0, v___x_2718_);
lean_ctor_set(v___x_2719_, 1, v_a_2714_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v___x_2719_);
v___x_2721_ = v___x_2716_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2724_, lean_object* v_declHint_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2724_, v_declHint_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2732_, lean_object* v_msg_2733_, lean_object* v_declHint_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v_a_2741_; lean_object* v___x_2742_; 
v___x_2740_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2733_, v_declHint_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref(v___x_2740_);
v___x_2742_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2732_, v_a_2741_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2743_, lean_object* v_msg_2744_, lean_object* v_declHint_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2743_, v_msg_2744_, v_declHint_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v_ref_2743_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2755_, lean_object* v_constName_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; uint8_t v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2762_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2763_ = 0;
lean_inc(v_constName_2756_);
v___x_2764_ = l_Lean_MessageData_ofConstName(v_constName_2756_, v___x_2763_);
v___x_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2765_, 0, v___x_2762_);
lean_ctor_set(v___x_2765_, 1, v___x_2764_);
v___x_2766_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2765_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2755_, v___x_2767_, v_constName_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2769_, lean_object* v_constName_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2769_, v_constName_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v_ref_2769_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_ref_2783_; lean_object* v___x_2784_; 
v_ref_2783_ = lean_ctor_get(v___y_2780_, 2);
v___x_2784_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2783_, v_constName_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
return v_res_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; lean_object* v_env_2799_; uint8_t v___x_2800_; lean_object* v___x_2801_; 
v___x_2798_ = lean_st_ref_get(v___y_2796_);
v_env_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc_ref(v_env_2799_);
lean_dec(v___x_2798_);
v___x_2800_ = 0;
lean_inc(v_constName_2792_);
v___x_2801_ = l_Lean_Environment_find_x3f(v_env_2799_, v_constName_2792_, v___x_2800_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2802_;
}
else
{
lean_object* v_val_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec(v_constName_2792_);
v_val_2803_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2801_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_val_2803_);
lean_dec(v___x_2801_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
lean_ctor_set_tag(v___x_2805_, 0);
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_val_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2817_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2818_, lean_object* v_as_2819_, size_t v_i_2820_, size_t v_stop_2821_){
_start:
{
uint8_t v___x_2822_; 
v___x_2822_ = lean_usize_dec_eq(v_i_2820_, v_stop_2821_);
if (v___x_2822_ == 0)
{
lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2823_ = lean_array_uget_borrowed(v_as_2819_, v_i_2820_);
v___x_2824_ = l_Lean_Expr_isAppOf(v_e_2818_, v___x_2823_);
if (v___x_2824_ == 0)
{
size_t v___x_2825_; size_t v___x_2826_; 
v___x_2825_ = ((size_t)1ULL);
v___x_2826_ = lean_usize_add(v_i_2820_, v___x_2825_);
v_i_2820_ = v___x_2826_;
goto _start;
}
else
{
return v___x_2824_;
}
}
else
{
uint8_t v___x_2828_; 
v___x_2828_ = 0;
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2829_, lean_object* v_as_2830_, lean_object* v_i_2831_, lean_object* v_stop_2832_){
_start:
{
size_t v_i_boxed_2833_; size_t v_stop_boxed_2834_; uint8_t v_res_2835_; lean_object* v_r_2836_; 
v_i_boxed_2833_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_stop_boxed_2834_ = lean_unbox_usize(v_stop_2832_);
lean_dec(v_stop_2832_);
v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2829_, v_as_2830_, v_i_boxed_2833_, v_stop_boxed_2834_);
lean_dec_ref(v_as_2830_);
lean_dec_ref(v_e_2829_);
v_r_2836_ = lean_box(v_res_2835_);
return v_r_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2837_, lean_object* v_name_2838_, lean_object* v___y_2839_, lean_object* v___x_2840_, lean_object* v_levels_2841_, lean_object* v_params_2842_, lean_object* v_e_2843_){
_start:
{
uint8_t v___x_2844_; 
v___x_2844_ = l_Lean_Expr_isApp(v_e_2843_);
if (v___x_2844_ == 0)
{
lean_object* v___x_2845_; 
lean_dec_ref(v_e_2843_);
lean_dec_ref(v_params_2842_);
lean_dec(v_levels_2841_);
lean_dec(v_name_2838_);
lean_dec(v_numParams_2837_);
v___x_2845_ = lean_box(0);
return v___x_2845_;
}
else
{
lean_object* v_dummy_2846_; lean_object* v_nargs_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_dummy_2846_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2847_ = l_Lean_Expr_getAppNumArgs(v_e_2843_);
lean_inc(v_nargs_2847_);
v___x_2848_ = lean_mk_array(v_nargs_2847_, v_dummy_2846_);
v___x_2849_ = lean_unsigned_to_nat(1u);
v___x_2850_ = lean_nat_sub(v_nargs_2847_, v___x_2849_);
lean_dec(v_nargs_2847_);
lean_inc_ref(v_e_2843_);
v___x_2851_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2843_, v___x_2848_, v___x_2850_);
v___x_2852_ = lean_array_get_size(v___x_2851_);
v___x_2853_ = l_Array_toSubarray___redArg(v___x_2851_, v_numParams_2837_, v___x_2852_);
v___x_2854_ = l_Lean_Expr_isAppOf(v_e_2843_, v_name_2838_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; uint8_t v___x_2856_; 
lean_dec(v_name_2838_);
v___x_2855_ = lean_array_get_size(v___y_2839_);
v___x_2856_ = lean_nat_dec_lt(v___x_2840_, v___x_2855_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
lean_dec_ref(v___x_2853_);
lean_dec_ref(v_e_2843_);
lean_dec_ref(v_params_2842_);
lean_dec(v_levels_2841_);
v___x_2857_ = lean_box(0);
return v___x_2857_;
}
else
{
if (v___x_2856_ == 0)
{
lean_object* v___x_2858_; 
lean_dec_ref(v___x_2853_);
lean_dec_ref(v_e_2843_);
lean_dec_ref(v_params_2842_);
lean_dec(v_levels_2841_);
v___x_2858_ = lean_box(0);
return v___x_2858_;
}
else
{
size_t v___x_2859_; size_t v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = lean_usize_of_nat(v___x_2855_);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2843_, v___y_2839_, v___x_2859_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec_ref(v___x_2853_);
lean_dec_ref(v_e_2843_);
lean_dec_ref(v_params_2842_);
lean_dec(v_levels_2841_);
v___x_2862_ = lean_box(0);
return v___x_2862_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2863_ = l_Lean_Expr_getAppFn(v_e_2843_);
lean_dec_ref(v_e_2843_);
v___x_2864_ = l_Lean_Expr_constName(v___x_2863_);
lean_dec_ref(v___x_2863_);
v___x_2865_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2864_);
v___x_2866_ = l_Lean_mkConst(v___x_2865_, v_levels_2841_);
v___x_2867_ = l_Subarray_copy___redArg(v___x_2853_);
v___x_2868_ = l_Array_append___redArg(v_params_2842_, v___x_2867_);
lean_dec_ref(v___x_2867_);
v___x_2869_ = l_Lean_mkAppN(v___x_2866_, v___x_2868_);
lean_dec_ref(v___x_2868_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
}
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_dec_ref(v_e_2843_);
v___x_2871_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2838_);
v___x_2872_ = l_Lean_mkConst(v___x_2871_, v_levels_2841_);
v___x_2873_ = l_Subarray_copy___redArg(v___x_2853_);
v___x_2874_ = l_Array_append___redArg(v_params_2842_, v___x_2873_);
lean_dec_ref(v___x_2873_);
v___x_2875_ = l_Lean_mkAppN(v___x_2872_, v___x_2874_);
lean_dec_ref(v___x_2874_);
v___x_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2877_, lean_object* v_name_2878_, lean_object* v___y_2879_, lean_object* v___x_2880_, lean_object* v_levels_2881_, lean_object* v_params_2882_, lean_object* v_e_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2877_, v_name_2878_, v___y_2879_, v___x_2880_, v_levels_2881_, v_params_2882_, v_e_2883_);
lean_dec(v___x_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v_eqProof_2885_, lean_object* v___x_2886_, lean_object* v_eNew_2887_, lean_object* v_snd_2888_, lean_object* v___x_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Meta_mkEqMP(v_eqProof_2885_, v___x_2886_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2897_, 0, v_eNew_2887_);
v___x_2898_ = lean_box(0);
v___x_2899_ = l_Lean_MVarId_replace(v_snd_2888_, v___x_2889_, v_a_2896_, v___x_2897_, v___x_2898_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
return v___x_2899_;
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v___x_2889_);
lean_dec(v_snd_2888_);
lean_dec_ref(v_eNew_2887_);
v_a_2900_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2895_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2895_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object* v_eqProof_2908_, lean_object* v___x_2909_, lean_object* v_eNew_2910_, lean_object* v_snd_2911_, lean_object* v___x_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_2908_, v___x_2909_, v_eNew_2910_, v_snd_2911_, v___x_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2918_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0));
v___x_2921_ = l_Lean_stringToMessageData(v___x_2920_);
return v___x_2921_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9));
v___x_2944_ = l_Lean_stringToMessageData(v___x_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_2945_, lean_object* v___x_2946_, lean_object* v___x_2947_, uint8_t v___x_2948_, lean_object* v___x_2949_, lean_object* v___x_2950_, uint8_t v___x_2951_, lean_object* v_params_2952_, lean_object* v_args_2953_, lean_object* v_indices_2954_, uint8_t v___x_2955_, lean_object* v_a_2956_, lean_object* v___x_2957_, lean_object* v___x_2958_, lean_object* v___f_2959_, lean_object* v___x_2960_, lean_object* v_targetArgs_2961_, lean_object* v_x_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v___x_2968_; uint8_t v___x_2969_; 
v___x_2968_ = lean_array_get_size(v_targetArgs_2961_);
v___x_2969_ = lean_nat_dec_eq(v___x_2968_, v___x_2945_);
if (v___x_2969_ == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v___x_2950_);
lean_dec(v___x_2949_);
lean_dec_ref(v___x_2947_);
v___x_2970_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_2971_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_2970_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
return v___x_2971_;
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_array_fget_borrowed(v_targetArgs_2961_, v___x_2946_);
lean_inc(v___y_2966_);
lean_inc_ref(v___y_2965_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc_ref(v___x_2947_);
v___x_2973_ = lean_infer_type(v___x_2947_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
if (lean_obj_tag(v_a_2974_) == 7)
{
lean_object* v_binderType_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v_binderType_2975_ = lean_ctor_get(v_a_2974_, 1);
lean_inc_ref(v_binderType_2975_);
lean_dec_ref_known(v_a_2974_, 3);
v___x_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_binderType_2975_);
v___x_2977_ = l_Lean_Meta_mkFreshExprMVar(v___x_2976_, v___x_2948_, v___x_2949_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = l_Lean_Expr_mvarId_x21(v_a_2978_);
v___x_2980_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2979_, v___x_2950_, v___x_2951_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
lean_inc(v___x_2972_);
v___x_2982_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2981_, v___x_2972_, v___y_2964_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3064_; 
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_2982_, 0);
lean_dec(v_unused_3065_);
v___x_2984_ = v___x_2982_;
v_isShared_2985_ = v_isSharedCheck_3064_;
goto v_resetjp_2983_;
}
else
{
lean_dec(v___x_2982_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3064_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2986_ = l_Lean_Expr_app___override(v___x_2947_, v_a_2978_);
lean_inc_ref(v_params_2952_);
v___x_2987_ = l_Array_append___redArg(v_params_2952_, v_args_2953_);
v___x_2988_ = l_Array_append___redArg(v___x_2987_, v_indices_2954_);
v___x_2989_ = l_Array_append___redArg(v___x_2988_, v_targetArgs_2961_);
v___x_2990_ = 1;
v___x_2991_ = l_Lean_Meta_mkLambdaFVars(v___x_2989_, v___x_2986_, v___x_2955_, v___x_2951_, v___x_2955_, v___x_2951_, v___x_2990_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec_ref(v___x_2989_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v___x_2993_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_2992_, v___y_2964_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = l_Lean_ConstantInfo_levelParams(v_a_2956_);
v___x_2996_ = l_Lean_mkCasesOnName(v___x_2957_);
v___x_2997_ = l_Lean_Meta_mkForallFVars(v_params_2952_, v___x_2958_, v___x_2955_, v___x_2951_, v___x_2951_, v___x_2990_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec_ref(v_params_2952_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_box(0);
lean_inc(v___x_2996_);
v___x_3000_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_2996_, v___x_2995_, v_a_2998_, v_a_2994_, v___x_2999_, v___y_2966_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
if (v_isShared_2985_ == 0)
{
lean_ctor_set_tag(v___x_2984_, 1);
lean_ctor_set(v___x_2984_, 0, v_a_3001_);
v___x_3003_ = v___x_2984_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3001_);
v___x_3003_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_addDecl(v___x_3003_, v___x_2955_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_dec_ref_known(v___x_3004_, 1);
v___x_3005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8));
v___x_3006_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3006_, 0, v___x_2996_);
lean_closure_set(v___x_3006_, 1, v___x_3005_);
v___x_3007_ = lean_box(0);
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_box(1);
v___x_3010_ = lean_mk_empty_array_with_capacity(v___x_2946_);
v___x_3011_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3011_, 0, v___x_3007_);
lean_ctor_set(v___x_3011_, 1, v___x_3008_);
lean_ctor_set(v___x_3011_, 2, v___x_3007_);
lean_ctor_set(v___x_3011_, 3, v___f_2959_);
lean_ctor_set(v___x_3011_, 4, v___x_3009_);
lean_ctor_set(v___x_3011_, 5, v___x_3009_);
lean_ctor_set(v___x_3011_, 6, v___x_3007_);
lean_ctor_set(v___x_3011_, 7, v___x_3010_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8, v___x_2951_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 1, v___x_2951_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 2, v___x_2951_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 3, v___x_2951_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 4, v___x_2955_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 5, v___x_2955_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 6, v___x_2955_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 7, v___x_2955_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 8, v___x_2951_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 9, v___x_2955_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*8 + 10, v___x_2951_);
v___x_3012_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3012_, 0, v___x_2960_);
lean_ctor_set(v___x_3012_, 1, v___x_3009_);
lean_ctor_set(v___x_3012_, 2, v___x_3008_);
lean_ctor_set(v___x_3012_, 3, v___x_3008_);
lean_ctor_set(v___x_3012_, 4, v___x_3008_);
lean_ctor_set(v___x_3012_, 5, v___x_3009_);
lean_ctor_set(v___x_3012_, 6, v___x_3008_);
v___x_3013_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3006_, v___x_3011_, v___x_3012_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3022_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3016_ = v___x_3013_;
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3022_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v_fst_3018_; lean_object* v___x_3020_; 
v_fst_3018_ = lean_ctor_get(v_a_3014_, 0);
lean_inc(v_fst_3018_);
lean_dec(v_a_3014_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v_fst_3018_);
v___x_3020_ = v___x_3016_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_fst_3018_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
v_a_3023_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3013_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3013_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
else
{
lean_dec(v___x_2996_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
return v___x_3004_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec(v___x_2996_);
lean_del_object(v___x_2984_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
v_a_3032_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3000_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3000_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec(v___x_2996_);
lean_dec(v___x_2995_);
lean_dec(v_a_2994_);
lean_del_object(v___x_2984_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
v_a_3040_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2997_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2997_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_del_object(v___x_2984_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
v_a_3048_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2993_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2993_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_del_object(v___x_2984_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
v_a_3056_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2991_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2991_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
else
{
lean_dec(v_a_2978_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v___x_2947_);
return v___x_2982_;
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v_a_2978_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v___x_2947_);
v_a_3066_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2980_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2980_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v___x_2950_);
lean_dec_ref(v___x_2947_);
v_a_3074_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2977_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_2977_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
lean_dec(v_a_2974_);
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v___x_2950_);
lean_dec(v___x_2949_);
lean_dec_ref(v___x_2947_);
v___x_3082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3083_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3082_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
return v___x_3083_;
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v___x_2960_);
lean_dec_ref(v___f_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v___x_2957_);
lean_dec_ref(v_params_2952_);
lean_dec_ref(v___x_2950_);
lean_dec(v___x_2949_);
lean_dec_ref(v___x_2947_);
v_a_3084_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_2973_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_2973_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3092_ = _args[0];
lean_object* v___x_3093_ = _args[1];
lean_object* v___x_3094_ = _args[2];
lean_object* v___x_3095_ = _args[3];
lean_object* v___x_3096_ = _args[4];
lean_object* v___x_3097_ = _args[5];
lean_object* v___x_3098_ = _args[6];
lean_object* v_params_3099_ = _args[7];
lean_object* v_args_3100_ = _args[8];
lean_object* v_indices_3101_ = _args[9];
lean_object* v___x_3102_ = _args[10];
lean_object* v_a_3103_ = _args[11];
lean_object* v___x_3104_ = _args[12];
lean_object* v___x_3105_ = _args[13];
lean_object* v___f_3106_ = _args[14];
lean_object* v___x_3107_ = _args[15];
lean_object* v_targetArgs_3108_ = _args[16];
lean_object* v_x_3109_ = _args[17];
lean_object* v___y_3110_ = _args[18];
lean_object* v___y_3111_ = _args[19];
lean_object* v___y_3112_ = _args[20];
lean_object* v___y_3113_ = _args[21];
lean_object* v___y_3114_ = _args[22];
_start:
{
uint8_t v___x_16314__boxed_3115_; uint8_t v___x_16317__boxed_3116_; uint8_t v___x_16318__boxed_3117_; lean_object* v_res_3118_; 
v___x_16314__boxed_3115_ = lean_unbox(v___x_3095_);
v___x_16317__boxed_3116_ = lean_unbox(v___x_3098_);
v___x_16318__boxed_3117_ = lean_unbox(v___x_3102_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3092_, v___x_3093_, v___x_3094_, v___x_16314__boxed_3115_, v___x_3096_, v___x_3097_, v___x_16317__boxed_3116_, v_params_3099_, v_args_3100_, v_indices_3101_, v___x_16318__boxed_3117_, v_a_3103_, v___x_3104_, v___x_3105_, v___f_3106_, v___x_3107_, v_targetArgs_3108_, v_x_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec_ref(v_x_3109_);
lean_dec_ref(v_targetArgs_3108_);
lean_dec_ref(v_a_3103_);
lean_dec_ref(v_indices_3101_);
lean_dec_ref(v_args_3100_);
lean_dec(v___x_3093_);
lean_dec(v___x_3092_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3119_, lean_object* v___x_3120_, lean_object* v___x_3121_, uint8_t v___x_3122_, lean_object* v___x_3123_, lean_object* v___x_3124_, uint8_t v___x_3125_, lean_object* v_params_3126_, lean_object* v_args_3127_, uint8_t v___x_3128_, lean_object* v_a_3129_, lean_object* v___x_3130_, lean_object* v___x_3131_, lean_object* v___f_3132_, lean_object* v___x_3133_, lean_object* v___x_3134_, lean_object* v_indices_3135_, lean_object* v_goalType_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___f_3146_; lean_object* v___x_3147_; 
v___x_3142_ = l_Lean_mkAppN(v___x_3119_, v_indices_3135_);
v___x_3143_ = lean_box(v___x_3122_);
v___x_3144_ = lean_box(v___x_3125_);
v___x_3145_ = lean_box(v___x_3128_);
v___f_3146_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 23, 16);
lean_closure_set(v___f_3146_, 0, v___x_3120_);
lean_closure_set(v___f_3146_, 1, v___x_3121_);
lean_closure_set(v___f_3146_, 2, v___x_3142_);
lean_closure_set(v___f_3146_, 3, v___x_3143_);
lean_closure_set(v___f_3146_, 4, v___x_3123_);
lean_closure_set(v___f_3146_, 5, v___x_3124_);
lean_closure_set(v___f_3146_, 6, v___x_3144_);
lean_closure_set(v___f_3146_, 7, v_params_3126_);
lean_closure_set(v___f_3146_, 8, v_args_3127_);
lean_closure_set(v___f_3146_, 9, v_indices_3135_);
lean_closure_set(v___f_3146_, 10, v___x_3145_);
lean_closure_set(v___f_3146_, 11, v_a_3129_);
lean_closure_set(v___f_3146_, 12, v___x_3130_);
lean_closure_set(v___f_3146_, 13, v___x_3131_);
lean_closure_set(v___f_3146_, 14, v___f_3132_);
lean_closure_set(v___f_3146_, 15, v___x_3133_);
v___x_3147_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3136_, v___x_3134_, v___f_3146_, v___x_3128_, v___x_3128_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
return v___x_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3148_ = _args[0];
lean_object* v___x_3149_ = _args[1];
lean_object* v___x_3150_ = _args[2];
lean_object* v___x_3151_ = _args[3];
lean_object* v___x_3152_ = _args[4];
lean_object* v___x_3153_ = _args[5];
lean_object* v___x_3154_ = _args[6];
lean_object* v_params_3155_ = _args[7];
lean_object* v_args_3156_ = _args[8];
lean_object* v___x_3157_ = _args[9];
lean_object* v_a_3158_ = _args[10];
lean_object* v___x_3159_ = _args[11];
lean_object* v___x_3160_ = _args[12];
lean_object* v___f_3161_ = _args[13];
lean_object* v___x_3162_ = _args[14];
lean_object* v___x_3163_ = _args[15];
lean_object* v_indices_3164_ = _args[16];
lean_object* v_goalType_3165_ = _args[17];
lean_object* v___y_3166_ = _args[18];
lean_object* v___y_3167_ = _args[19];
lean_object* v___y_3168_ = _args[20];
lean_object* v___y_3169_ = _args[21];
lean_object* v___y_3170_ = _args[22];
_start:
{
uint8_t v___x_16650__boxed_3171_; uint8_t v___x_16653__boxed_3172_; uint8_t v___x_16654__boxed_3173_; lean_object* v_res_3174_; 
v___x_16650__boxed_3171_ = lean_unbox(v___x_3151_);
v___x_16653__boxed_3172_ = lean_unbox(v___x_3154_);
v___x_16654__boxed_3173_ = lean_unbox(v___x_3157_);
v_res_3174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3148_, v___x_3149_, v___x_3150_, v___x_16650__boxed_3171_, v___x_3152_, v___x_3153_, v___x_16653__boxed_3172_, v_params_3155_, v_args_3156_, v___x_16654__boxed_3173_, v_a_3158_, v___x_3159_, v___x_3160_, v___f_3161_, v___x_3162_, v___x_3163_, v_indices_3164_, v_goalType_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object* v___x_3175_, uint8_t v___x_3176_, lean_object* v_snd_3177_, lean_object* v___x_3178_, uint8_t v___x_3179_, lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v_a_3182_, lean_object* v___x_3183_, lean_object* v___x_3184_, uint8_t v___x_3185_, lean_object* v___x_3186_, lean_object* v_params_3187_, lean_object* v_args_3188_, lean_object* v_a_3189_, lean_object* v___x_3190_, lean_object* v___x_3191_, lean_object* v___f_3192_, lean_object* v___x_3193_, lean_object* v___x_3194_, lean_object* v_numIndices_3195_, lean_object* v_goalType_3196_, lean_object* v___x_3197_, lean_object* v___x_3198_, lean_object* v_fst_3199_, lean_object* v___x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_lctx_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_lctx_3206_ = lean_ctor_get(v___y_3201_, 2);
lean_inc(v___x_3175_);
lean_inc_ref(v_lctx_3206_);
v___x_3207_ = l_Lean_LocalContext_get_x21(v_lctx_3206_, v___x_3175_);
v___x_3208_ = l_Lean_LocalDecl_type(v___x_3207_);
lean_dec_ref(v___x_3207_);
v___x_3209_ = 2;
v___x_3210_ = lean_box(0);
v___x_3211_ = 0;
v___x_3212_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*1, v___x_3209_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*1 + 1, v___x_3176_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*1 + 2, v___x_3211_);
lean_inc_ref(v___x_3178_);
lean_inc(v_snd_3177_);
v___x_3213_ = l_Lean_MVarId_rewrite(v_snd_3177_, v___x_3208_, v___x_3178_, v___x_3176_, v___x_3212_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v_eNew_3215_; lean_object* v_eqProof_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
lean_dec_ref_known(v___x_3213_, 1);
v_eNew_3215_ = lean_ctor_get(v_a_3214_, 0);
lean_inc_ref(v_eNew_3215_);
v_eqProof_3216_ = lean_ctor_get(v_a_3214_, 1);
lean_inc_ref(v_eqProof_3216_);
lean_dec(v_a_3214_);
lean_inc(v___x_3175_);
v___x_3217_ = l_Lean_mkFVar(v___x_3175_);
lean_inc(v_snd_3177_);
v___f_3218_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3218_, 0, v_eqProof_3216_);
lean_closure_set(v___f_3218_, 1, v___x_3217_);
lean_closure_set(v___f_3218_, 2, v_eNew_3215_);
lean_closure_set(v___f_3218_, 3, v_snd_3177_);
lean_closure_set(v___f_3218_, 4, v___x_3175_);
v___x_3219_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3177_, v___f_3218_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___y_3222_; uint8_t v___x_3250_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v___x_3250_ = lean_nat_dec_lt(v___x_3197_, v___x_3198_);
if (v___x_3250_ == 0)
{
v___y_3222_ = v_fst_3199_;
goto v___jp_3221_;
}
else
{
lean_object* v_fvarId_3251_; lean_object* v_xs_x27_3252_; lean_object* v___x_3253_; 
v_fvarId_3251_ = lean_ctor_get(v_a_3220_, 0);
v_xs_x27_3252_ = lean_array_fset(v_fst_3199_, v___x_3197_, v___x_3200_);
lean_inc(v_fvarId_3251_);
v___x_3253_ = lean_array_fset(v_xs_x27_3252_, v___x_3197_, v_fvarId_3251_);
v___y_3222_ = v___x_3253_;
goto v___jp_3221_;
}
v___jp_3221_:
{
lean_object* v_mvarId_3223_; lean_object* v___x_3224_; 
v_mvarId_3223_ = lean_ctor_get(v_a_3220_, 1);
lean_inc(v_mvarId_3223_);
lean_dec(v_a_3220_);
v___x_3224_ = l_Lean_MVarId_revert(v_mvarId_3223_, v___y_3222_, v___x_3179_, v___x_3179_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v_snd_3226_; lean_object* v___x_3227_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v_snd_3226_ = lean_ctor_get(v_a_3225_, 1);
lean_inc(v_snd_3226_);
lean_dec(v_a_3225_);
v___x_3227_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3226_, v___x_3180_, v___y_3202_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3240_; 
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v___x_3227_, 0);
lean_dec(v_unused_3241_);
v___x_3229_ = v___x_3227_;
v_isShared_3230_ = v_isSharedCheck_3240_;
goto v_resetjp_3228_;
}
else
{
lean_dec(v___x_3227_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3240_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___f_3235_; lean_object* v___x_3237_; 
v___x_3231_ = l_Lean_Expr_app___override(v___x_3181_, v_a_3182_);
v___x_3232_ = lean_box(v___x_3185_);
v___x_3233_ = lean_box(v___x_3176_);
v___x_3234_ = lean_box(v___x_3179_);
v___f_3235_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 23, 16);
lean_closure_set(v___f_3235_, 0, v___x_3231_);
lean_closure_set(v___f_3235_, 1, v___x_3183_);
lean_closure_set(v___f_3235_, 2, v___x_3184_);
lean_closure_set(v___f_3235_, 3, v___x_3232_);
lean_closure_set(v___f_3235_, 4, v___x_3186_);
lean_closure_set(v___f_3235_, 5, v___x_3178_);
lean_closure_set(v___f_3235_, 6, v___x_3233_);
lean_closure_set(v___f_3235_, 7, v_params_3187_);
lean_closure_set(v___f_3235_, 8, v_args_3188_);
lean_closure_set(v___f_3235_, 9, v___x_3234_);
lean_closure_set(v___f_3235_, 10, v_a_3189_);
lean_closure_set(v___f_3235_, 11, v___x_3190_);
lean_closure_set(v___f_3235_, 12, v___x_3191_);
lean_closure_set(v___f_3235_, 13, v___f_3192_);
lean_closure_set(v___f_3235_, 14, v___x_3193_);
lean_closure_set(v___f_3235_, 15, v___x_3194_);
if (v_isShared_3230_ == 0)
{
lean_ctor_set_tag(v___x_3229_, 1);
lean_ctor_set(v___x_3229_, 0, v_numIndices_3195_);
v___x_3237_ = v___x_3229_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_numIndices_3195_);
v___x_3237_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3196_, v___x_3237_, v___f_3235_, v___x_3179_, v___x_3179_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_);
lean_dec_ref(v___y_3201_);
return v___x_3238_;
}
}
}
else
{
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_goalType_3196_);
lean_dec(v_numIndices_3195_);
lean_dec(v___x_3194_);
lean_dec(v___x_3193_);
lean_dec_ref(v___f_3192_);
lean_dec_ref(v___x_3191_);
lean_dec(v___x_3190_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_args_3188_);
lean_dec_ref(v_params_3187_);
lean_dec(v___x_3186_);
lean_dec(v___x_3184_);
lean_dec(v___x_3183_);
lean_dec_ref(v_a_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v___x_3178_);
return v___x_3227_;
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_goalType_3196_);
lean_dec(v_numIndices_3195_);
lean_dec(v___x_3194_);
lean_dec(v___x_3193_);
lean_dec_ref(v___f_3192_);
lean_dec_ref(v___x_3191_);
lean_dec(v___x_3190_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_args_3188_);
lean_dec_ref(v_params_3187_);
lean_dec(v___x_3186_);
lean_dec(v___x_3184_);
lean_dec(v___x_3183_);
lean_dec_ref(v_a_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v___x_3180_);
lean_dec_ref(v___x_3178_);
v_a_3242_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3224_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3224_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_fst_3199_);
lean_dec_ref(v_goalType_3196_);
lean_dec(v_numIndices_3195_);
lean_dec(v___x_3194_);
lean_dec(v___x_3193_);
lean_dec_ref(v___f_3192_);
lean_dec_ref(v___x_3191_);
lean_dec(v___x_3190_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_args_3188_);
lean_dec_ref(v_params_3187_);
lean_dec(v___x_3186_);
lean_dec(v___x_3184_);
lean_dec(v___x_3183_);
lean_dec_ref(v_a_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v___x_3180_);
lean_dec_ref(v___x_3178_);
v_a_3254_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3219_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3219_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_fst_3199_);
lean_dec_ref(v_goalType_3196_);
lean_dec(v_numIndices_3195_);
lean_dec(v___x_3194_);
lean_dec(v___x_3193_);
lean_dec_ref(v___f_3192_);
lean_dec_ref(v___x_3191_);
lean_dec(v___x_3190_);
lean_dec_ref(v_a_3189_);
lean_dec_ref(v_args_3188_);
lean_dec_ref(v_params_3187_);
lean_dec(v___x_3186_);
lean_dec(v___x_3184_);
lean_dec(v___x_3183_);
lean_dec_ref(v_a_3182_);
lean_dec_ref(v___x_3181_);
lean_dec_ref(v___x_3180_);
lean_dec_ref(v___x_3178_);
lean_dec(v_snd_3177_);
lean_dec(v___x_3175_);
v_a_3262_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3213_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3213_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object** _args){
lean_object* v___x_3270_ = _args[0];
lean_object* v___x_3271_ = _args[1];
lean_object* v_snd_3272_ = _args[2];
lean_object* v___x_3273_ = _args[3];
lean_object* v___x_3274_ = _args[4];
lean_object* v___x_3275_ = _args[5];
lean_object* v___x_3276_ = _args[6];
lean_object* v_a_3277_ = _args[7];
lean_object* v___x_3278_ = _args[8];
lean_object* v___x_3279_ = _args[9];
lean_object* v___x_3280_ = _args[10];
lean_object* v___x_3281_ = _args[11];
lean_object* v_params_3282_ = _args[12];
lean_object* v_args_3283_ = _args[13];
lean_object* v_a_3284_ = _args[14];
lean_object* v___x_3285_ = _args[15];
lean_object* v___x_3286_ = _args[16];
lean_object* v___f_3287_ = _args[17];
lean_object* v___x_3288_ = _args[18];
lean_object* v___x_3289_ = _args[19];
lean_object* v_numIndices_3290_ = _args[20];
lean_object* v_goalType_3291_ = _args[21];
lean_object* v___x_3292_ = _args[22];
lean_object* v___x_3293_ = _args[23];
lean_object* v_fst_3294_ = _args[24];
lean_object* v___x_3295_ = _args[25];
lean_object* v___y_3296_ = _args[26];
lean_object* v___y_3297_ = _args[27];
lean_object* v___y_3298_ = _args[28];
lean_object* v___y_3299_ = _args[29];
lean_object* v___y_3300_ = _args[30];
_start:
{
uint8_t v___x_16717__boxed_3301_; uint8_t v___x_16720__boxed_3302_; uint8_t v___x_16726__boxed_3303_; lean_object* v_res_3304_; 
v___x_16717__boxed_3301_ = lean_unbox(v___x_3271_);
v___x_16720__boxed_3302_ = lean_unbox(v___x_3274_);
v___x_16726__boxed_3303_ = lean_unbox(v___x_3280_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3270_, v___x_16717__boxed_3301_, v_snd_3272_, v___x_3273_, v___x_16720__boxed_3302_, v___x_3275_, v___x_3276_, v_a_3277_, v___x_3278_, v___x_3279_, v___x_16726__boxed_3303_, v___x_3281_, v_params_3282_, v_args_3283_, v_a_3284_, v___x_3285_, v___x_3286_, v___f_3287_, v___x_3288_, v___x_3289_, v_numIndices_3290_, v_goalType_3291_, v___x_3292_, v___x_3293_, v_fst_3294_, v___x_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___x_3293_);
lean_dec(v___x_3292_);
return v_res_3304_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t v___x_3305_, lean_object* v_x_3306_){
_start:
{
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object* v___x_3307_, lean_object* v_x_3308_){
_start:
{
uint8_t v___x_16916__boxed_3309_; uint8_t v_res_3310_; lean_object* v_r_3311_; 
v___x_16916__boxed_3309_ = lean_unbox(v___x_3307_);
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_16916__boxed_3309_, v_x_3308_);
lean_dec(v_x_3308_);
v_r_3311_ = lean_box(v_res_3310_);
return v_r_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object* v___x_3315_, lean_object* v_a_3316_, lean_object* v___x_3317_, lean_object* v_numIndices_3318_, lean_object* v___x_3319_, lean_object* v___x_3320_, lean_object* v___x_3321_, lean_object* v_params_3322_, lean_object* v_a_3323_, lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v___x_3326_, lean_object* v___x_3327_, lean_object* v_args_3328_, lean_object* v_goalType_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3335_ = lean_array_get_size(v_args_3328_);
v___x_3336_ = lean_nat_dec_eq(v___x_3335_, v___x_3315_);
if (v___x_3336_ == 0)
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec_ref(v_goalType_3329_);
lean_dec_ref(v_args_3328_);
lean_dec(v___x_3326_);
lean_dec_ref(v___x_3325_);
lean_dec(v___x_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_params_3322_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___x_3320_);
lean_dec(v_numIndices_3318_);
lean_dec(v___x_3317_);
lean_dec(v___x_3315_);
v___x_3337_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3338_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3337_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3338_;
}
else
{
if (lean_obj_tag(v_a_3316_) == 7)
{
lean_object* v_binderType_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_binderType_3339_ = lean_ctor_get(v_a_3316_, 1);
v___x_3340_ = lean_array_fget(v_args_3328_, v___x_3317_);
lean_inc_ref(v_binderType_3339_);
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_binderType_3339_);
v___x_3342_ = 0;
v___x_3343_ = lean_box(0);
v___x_3344_ = l_Lean_Meta_mkFreshExprMVar(v___x_3341_, v___x_3342_, v___x_3343_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = l_Lean_Expr_mvarId_x21(v_a_3345_);
v___x_3347_ = lean_nat_add(v_numIndices_3318_, v___x_3315_);
v___x_3348_ = lean_box(0);
v___x_3349_ = 0;
v___f_3350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0));
v___x_3351_ = l_Lean_Meta_introNCore(v___x_3346_, v___x_3347_, v___x_3348_, v___x_3349_, v___x_3349_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___f_3361_; lean_object* v___x_3362_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v_fst_3353_ = lean_ctor_get(v_a_3352_, 0);
lean_inc(v_fst_3353_);
v_snd_3354_ = lean_ctor_get(v_a_3352_, 1);
lean_inc_n(v_snd_3354_, 2);
lean_dec(v_a_3352_);
v___x_3355_ = lean_array_get_size(v_fst_3353_);
v___x_3356_ = lean_nat_sub(v___x_3355_, v___x_3315_);
v___x_3357_ = lean_array_get(v___x_3319_, v_fst_3353_, v___x_3356_);
v___x_3358_ = lean_box(v___x_3336_);
v___x_3359_ = lean_box(v___x_3349_);
v___x_3360_ = lean_box(v___x_3342_);
v___f_3361_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed), 31, 26);
lean_closure_set(v___f_3361_, 0, v___x_3357_);
lean_closure_set(v___f_3361_, 1, v___x_3358_);
lean_closure_set(v___f_3361_, 2, v_snd_3354_);
lean_closure_set(v___f_3361_, 3, v___x_3320_);
lean_closure_set(v___f_3361_, 4, v___x_3359_);
lean_closure_set(v___f_3361_, 5, v___x_3340_);
lean_closure_set(v___f_3361_, 6, v___x_3321_);
lean_closure_set(v___f_3361_, 7, v_a_3345_);
lean_closure_set(v___f_3361_, 8, v___x_3315_);
lean_closure_set(v___f_3361_, 9, v___x_3317_);
lean_closure_set(v___f_3361_, 10, v___x_3360_);
lean_closure_set(v___f_3361_, 11, v___x_3343_);
lean_closure_set(v___f_3361_, 12, v_params_3322_);
lean_closure_set(v___f_3361_, 13, v_args_3328_);
lean_closure_set(v___f_3361_, 14, v_a_3323_);
lean_closure_set(v___f_3361_, 15, v___x_3324_);
lean_closure_set(v___f_3361_, 16, v___x_3325_);
lean_closure_set(v___f_3361_, 17, v___f_3350_);
lean_closure_set(v___f_3361_, 18, v___x_3348_);
lean_closure_set(v___f_3361_, 19, v___x_3326_);
lean_closure_set(v___f_3361_, 20, v_numIndices_3318_);
lean_closure_set(v___f_3361_, 21, v_goalType_3329_);
lean_closure_set(v___f_3361_, 22, v___x_3356_);
lean_closure_set(v___f_3361_, 23, v___x_3355_);
lean_closure_set(v___f_3361_, 24, v_fst_3353_);
lean_closure_set(v___f_3361_, 25, v___x_3327_);
v___x_3362_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3354_, v___f_3361_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3362_;
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v_a_3345_);
lean_dec(v___x_3340_);
lean_dec_ref(v_goalType_3329_);
lean_dec_ref(v_args_3328_);
lean_dec(v___x_3326_);
lean_dec_ref(v___x_3325_);
lean_dec(v___x_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_params_3322_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___x_3320_);
lean_dec(v_numIndices_3318_);
lean_dec(v___x_3317_);
lean_dec(v___x_3315_);
v_a_3363_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3351_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3351_);
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
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec(v___x_3340_);
lean_dec_ref(v_goalType_3329_);
lean_dec_ref(v_args_3328_);
lean_dec(v___x_3326_);
lean_dec_ref(v___x_3325_);
lean_dec(v___x_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_params_3322_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___x_3320_);
lean_dec(v_numIndices_3318_);
lean_dec(v___x_3317_);
lean_dec(v___x_3315_);
v_a_3371_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3344_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3344_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec_ref(v_goalType_3329_);
lean_dec_ref(v_args_3328_);
lean_dec(v___x_3326_);
lean_dec_ref(v___x_3325_);
lean_dec(v___x_3324_);
lean_dec_ref(v_a_3323_);
lean_dec_ref(v_params_3322_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___x_3320_);
lean_dec(v_numIndices_3318_);
lean_dec(v___x_3317_);
lean_dec(v___x_3315_);
v___x_3379_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3380_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3379_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object** _args){
lean_object* v___x_3381_ = _args[0];
lean_object* v_a_3382_ = _args[1];
lean_object* v___x_3383_ = _args[2];
lean_object* v_numIndices_3384_ = _args[3];
lean_object* v___x_3385_ = _args[4];
lean_object* v___x_3386_ = _args[5];
lean_object* v___x_3387_ = _args[6];
lean_object* v_params_3388_ = _args[7];
lean_object* v_a_3389_ = _args[8];
lean_object* v___x_3390_ = _args[9];
lean_object* v___x_3391_ = _args[10];
lean_object* v___x_3392_ = _args[11];
lean_object* v___x_3393_ = _args[12];
lean_object* v_args_3394_ = _args[13];
lean_object* v_goalType_3395_ = _args[14];
lean_object* v___y_3396_ = _args[15];
lean_object* v___y_3397_ = _args[16];
lean_object* v___y_3398_ = _args[17];
lean_object* v___y_3399_ = _args[18];
lean_object* v___y_3400_ = _args[19];
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3381_, v_a_3382_, v___x_3383_, v_numIndices_3384_, v___x_3385_, v___x_3386_, v___x_3387_, v_params_3388_, v_a_3389_, v___x_3390_, v___x_3391_, v___x_3392_, v___x_3393_, v_args_3394_, v_goalType_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___x_3385_);
lean_dec_ref(v_a_3382_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v___x_3408_; lean_object* v_env_3409_; uint8_t v___x_3410_; lean_object* v___x_3411_; 
v___x_3408_ = lean_st_ref_get(v___y_3406_);
v_env_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc_ref(v_env_3409_);
lean_dec(v___x_3408_);
v___x_3410_ = 0;
lean_inc(v_constName_3402_);
v___x_3411_ = l_Lean_Environment_findConstVal_x3f(v_env_3409_, v_constName_3402_, v___x_3410_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
return v___x_3412_;
}
else
{
lean_object* v_val_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_constName_3402_);
v_val_3413_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3411_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_val_3413_);
lean_dec(v___x_3411_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set_tag(v___x_3415_, 0);
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_val_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3434_; 
lean_inc(v_constName_3428_);
v___x_3434_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3446_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3437_ = v___x_3434_;
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3434_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3446_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v_levelParams_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v_levelParams_3439_ = lean_ctor_get(v_a_3435_, 1);
lean_inc(v_levelParams_3439_);
lean_dec(v_a_3435_);
v___x_3440_ = lean_box(0);
v___x_3441_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3439_, v___x_3440_);
v___x_3442_ = l_Lean_mkConst(v_constName_3428_, v___x_3441_);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3442_);
v___x_3444_ = v___x_3437_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v_constName_3428_);
v_a_3447_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3434_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3434_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v___y_3464_, lean_object* v_levels_3465_, lean_object* v_params_3466_, lean_object* v_predicates_3467_, lean_object* v_as_3468_, size_t v_sz_3469_, size_t v_i_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_usize_dec_lt(v_i_3470_, v_sz_3469_);
if (v___x_3477_ == 0)
{
lean_object* v___x_3478_; 
lean_dec_ref(v_params_3466_);
lean_dec(v_levels_3465_);
lean_dec_ref(v___y_3464_);
v___x_3478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3478_, 0, v_b_3471_);
return v___x_3478_;
}
else
{
lean_object* v_a_3479_; lean_object* v_toConstantVal_3480_; lean_object* v_numParams_3481_; lean_object* v_numIndices_3482_; lean_object* v_name_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___f_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_a_3479_ = lean_array_uget_borrowed(v_as_3468_, v_i_3470_);
v_toConstantVal_3480_ = lean_ctor_get(v_a_3479_, 0);
v_numParams_3481_ = lean_ctor_get(v_a_3479_, 1);
v_numIndices_3482_ = lean_ctor_get(v_a_3479_, 2);
v_name_3483_ = lean_ctor_get(v_toConstantVal_3480_, 0);
v___x_3484_ = lean_unsigned_to_nat(0u);
v___x_3485_ = lean_box(0);
v___x_3486_ = lean_box(0);
lean_inc_ref(v_params_3466_);
lean_inc(v_levels_3465_);
lean_inc_ref(v___y_3464_);
lean_inc_n(v_name_3483_, 2);
lean_inc(v_numParams_3481_);
v___f_3487_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3487_, 0, v_numParams_3481_);
lean_closure_set(v___f_3487_, 1, v_name_3483_);
lean_closure_set(v___f_3487_, 2, v___y_3464_);
lean_closure_set(v___f_3487_, 3, v___x_3484_);
lean_closure_set(v___f_3487_, 4, v_levels_3465_);
lean_closure_set(v___f_3487_, 5, v_params_3466_);
v___x_3488_ = l_Lean_mkCasesOnName(v_name_3483_);
lean_inc(v___x_3488_);
v___x_3489_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3488_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v___x_3491_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3488_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
lean_inc_ref(v_params_3466_);
v___x_3493_ = l_Array_append___redArg(v_params_3466_, v_predicates_3467_);
v___x_3494_ = l_Lean_mkAppN(v_a_3492_, v___x_3493_);
lean_dec_ref(v___x_3493_);
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3474_);
lean_inc(v___y_3473_);
lean_inc_ref(v___y_3472_);
lean_inc_ref(v___x_3494_);
v___x_3495_ = lean_infer_type(v___x_3494_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = lean_replace_expr(v___f_3487_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v___f_3487_);
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3474_);
lean_inc(v___y_3473_);
lean_inc_ref(v___y_3472_);
lean_inc_ref(v___x_3494_);
v___x_3498_ = lean_infer_type(v___x_3494_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___f_3506_; uint8_t v___x_3507_; lean_object* v___x_3508_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
lean_inc(v_name_3483_);
v___x_3500_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3483_);
v___x_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3500_);
v___x_3502_ = l_Lean_Name_append(v___x_3500_, v___x_3501_);
lean_inc(v_levels_3465_);
v___x_3503_ = l_Lean_mkConst(v___x_3502_, v_levels_3465_);
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3497_);
lean_inc_ref(v_params_3466_);
lean_inc(v_numIndices_3482_);
v___f_3506_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed), 20, 13);
lean_closure_set(v___f_3506_, 0, v___x_3504_);
lean_closure_set(v___f_3506_, 1, v_a_3499_);
lean_closure_set(v___f_3506_, 2, v___x_3484_);
lean_closure_set(v___f_3506_, 3, v_numIndices_3482_);
lean_closure_set(v___f_3506_, 4, v___x_3485_);
lean_closure_set(v___f_3506_, 5, v___x_3503_);
lean_closure_set(v___f_3506_, 6, v___x_3494_);
lean_closure_set(v___f_3506_, 7, v_params_3466_);
lean_closure_set(v___f_3506_, 8, v_a_3490_);
lean_closure_set(v___f_3506_, 9, v___x_3500_);
lean_closure_set(v___f_3506_, 10, v___x_3497_);
lean_closure_set(v___f_3506_, 11, v___x_3505_);
lean_closure_set(v___f_3506_, 12, v___x_3486_);
v___x_3507_ = 0;
v___x_3508_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_3497_, v___x_3505_, v___f_3506_, v___x_3507_, v___x_3507_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3508_) == 0)
{
size_t v___x_3509_; size_t v___x_3510_; 
lean_dec_ref_known(v___x_3508_, 1);
v___x_3509_ = ((size_t)1ULL);
v___x_3510_ = lean_usize_add(v_i_3470_, v___x_3509_);
v_i_3470_ = v___x_3510_;
v_b_3471_ = v___x_3486_;
goto _start;
}
else
{
lean_dec_ref(v_params_3466_);
lean_dec(v_levels_3465_);
lean_dec_ref(v___y_3464_);
return v___x_3508_;
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v___x_3497_);
lean_dec_ref(v___x_3494_);
lean_dec(v_a_3490_);
lean_dec_ref(v_params_3466_);
lean_dec(v_levels_3465_);
lean_dec_ref(v___y_3464_);
v_a_3512_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3498_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3498_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v___x_3494_);
lean_dec(v_a_3490_);
lean_dec_ref(v___f_3487_);
lean_dec_ref(v_params_3466_);
lean_dec(v_levels_3465_);
lean_dec_ref(v___y_3464_);
v_a_3520_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3495_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3495_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_a_3490_);
lean_dec_ref(v___f_3487_);
lean_dec_ref(v_params_3466_);
lean_dec(v_levels_3465_);
lean_dec_ref(v___y_3464_);
v_a_3528_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3491_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3491_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v___x_3488_);
lean_dec_ref(v___f_3487_);
lean_dec_ref(v_params_3466_);
lean_dec(v_levels_3465_);
lean_dec_ref(v___y_3464_);
v_a_3536_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3489_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3489_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v___y_3544_, lean_object* v_levels_3545_, lean_object* v_params_3546_, lean_object* v_predicates_3547_, lean_object* v_as_3548_, lean_object* v_sz_3549_, lean_object* v_i_3550_, lean_object* v_b_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
size_t v_sz_boxed_3557_; size_t v_i_boxed_3558_; lean_object* v_res_3559_; 
v_sz_boxed_3557_ = lean_unbox_usize(v_sz_3549_);
lean_dec(v_sz_3549_);
v_i_boxed_3558_ = lean_unbox_usize(v_i_3550_);
lean_dec(v_i_3550_);
v_res_3559_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3544_, v_levels_3545_, v_params_3546_, v_predicates_3547_, v_as_3548_, v_sz_boxed_3557_, v_i_boxed_3558_, v_b_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec_ref(v_as_3548_);
lean_dec_ref(v_predicates_3547_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3560_, size_t v_sz_3561_, size_t v_i_3562_, lean_object* v_bs_3563_){
_start:
{
uint8_t v___x_3564_; 
v___x_3564_ = lean_usize_dec_lt(v_i_3562_, v_sz_3561_);
if (v___x_3564_ == 0)
{
lean_dec(v_levels_3560_);
return v_bs_3563_;
}
else
{
lean_object* v_v_3565_; lean_object* v_toConstantVal_3566_; lean_object* v_name_3567_; lean_object* v___x_3568_; lean_object* v_bs_x27_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; size_t v___x_3572_; size_t v___x_3573_; lean_object* v___x_3574_; 
v_v_3565_ = lean_array_uget_borrowed(v_bs_3563_, v_i_3562_);
v_toConstantVal_3566_ = lean_ctor_get(v_v_3565_, 0);
v_name_3567_ = lean_ctor_get(v_toConstantVal_3566_, 0);
lean_inc(v_name_3567_);
v___x_3568_ = lean_unsigned_to_nat(0u);
v_bs_x27_3569_ = lean_array_uset(v_bs_3563_, v_i_3562_, v___x_3568_);
v___x_3570_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3567_);
lean_inc(v_levels_3560_);
v___x_3571_ = l_Lean_mkConst(v___x_3570_, v_levels_3560_);
v___x_3572_ = ((size_t)1ULL);
v___x_3573_ = lean_usize_add(v_i_3562_, v___x_3572_);
v___x_3574_ = lean_array_uset(v_bs_x27_3569_, v_i_3562_, v___x_3571_);
v_i_3562_ = v___x_3573_;
v_bs_3563_ = v___x_3574_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3576_, lean_object* v_sz_3577_, lean_object* v_i_3578_, lean_object* v_bs_3579_){
_start:
{
size_t v_sz_boxed_3580_; size_t v_i_boxed_3581_; lean_object* v_res_3582_; 
v_sz_boxed_3580_ = lean_unbox_usize(v_sz_3577_);
lean_dec(v_sz_3577_);
v_i_boxed_3581_ = lean_unbox_usize(v_i_3578_);
lean_dec(v_i_3578_);
v_res_3582_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3576_, v_sz_boxed_3580_, v_i_boxed_3581_, v_bs_3579_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3583_, lean_object* v_levels_3584_, lean_object* v___y_3585_, lean_object* v_params_3586_, lean_object* v_x_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
size_t v_sz_3593_; size_t v___x_3594_; lean_object* v_predicates_3595_; size_t v_sz_3596_; lean_object* v_predicates_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_sz_3593_ = lean_array_size(v_infos_3583_);
v___x_3594_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3583_);
lean_inc(v_levels_3584_);
v_predicates_3595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3584_, v_sz_3593_, v___x_3594_, v_infos_3583_);
v_sz_3596_ = lean_array_size(v_predicates_3595_);
v_predicates_3597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3586_, v_sz_3596_, v___x_3594_, v_predicates_3595_);
v___x_3598_ = lean_box(0);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3585_, v_levels_3584_, v_params_3586_, v_predicates_3597_, v_infos_3583_, v_sz_3593_, v___x_3594_, v___x_3598_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec_ref(v_infos_3583_);
lean_dec_ref(v_predicates_3597_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3606_ == 0)
{
lean_object* v_unused_3607_; 
v_unused_3607_ = lean_ctor_get(v___x_3599_, 0);
lean_dec(v_unused_3607_);
v___x_3601_ = v___x_3599_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_dec(v___x_3599_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3598_);
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3598_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
else
{
return v___x_3599_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3608_, lean_object* v_levels_3609_, lean_object* v___y_3610_, lean_object* v_params_3611_, lean_object* v_x_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3608_, v_levels_3609_, v___y_3610_, v_params_3611_, v_x_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec_ref(v_x_3612_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3619_, size_t v_i_3620_, size_t v_stop_3621_, lean_object* v_b_3622_){
_start:
{
uint8_t v___x_3623_; 
v___x_3623_ = lean_usize_dec_eq(v_i_3620_, v_stop_3621_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; lean_object* v_ctors_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; size_t v___x_3628_; size_t v___x_3629_; 
v___x_3624_ = lean_array_uget_borrowed(v_as_3619_, v_i_3620_);
v_ctors_3625_ = lean_ctor_get(v___x_3624_, 4);
lean_inc(v_ctors_3625_);
v___x_3626_ = lean_array_mk(v_ctors_3625_);
v___x_3627_ = l_Array_append___redArg(v_b_3622_, v___x_3626_);
lean_dec_ref(v___x_3626_);
v___x_3628_ = ((size_t)1ULL);
v___x_3629_ = lean_usize_add(v_i_3620_, v___x_3628_);
v_i_3620_ = v___x_3629_;
v_b_3622_ = v___x_3627_;
goto _start;
}
else
{
return v_b_3622_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3631_, lean_object* v_i_3632_, lean_object* v_stop_3633_, lean_object* v_b_3634_){
_start:
{
size_t v_i_boxed_3635_; size_t v_stop_boxed_3636_; lean_object* v_res_3637_; 
v_i_boxed_3635_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_stop_boxed_3636_ = lean_unbox_usize(v_stop_3633_);
lean_dec(v_stop_3633_);
v_res_3637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3631_, v_i_boxed_3635_, v_stop_boxed_3636_, v_b_3634_);
lean_dec_ref(v_as_3631_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v_toConstantVal_3649_; lean_object* v_numParams_3650_; lean_object* v_levelParams_3651_; lean_object* v_type_3652_; lean_object* v___x_3653_; lean_object* v_levels_3654_; lean_object* v___y_3656_; lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v___x_3646_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3647_ = lean_unsigned_to_nat(0u);
v___x_3648_ = lean_array_get_borrowed(v___x_3646_, v_infos_3640_, v___x_3647_);
v_toConstantVal_3649_ = lean_ctor_get(v___x_3648_, 0);
v_numParams_3650_ = lean_ctor_get(v___x_3648_, 1);
lean_inc(v_numParams_3650_);
v_levelParams_3651_ = lean_ctor_get(v_toConstantVal_3649_, 1);
v_type_3652_ = lean_ctor_get(v_toConstantVal_3649_, 2);
lean_inc_ref(v_type_3652_);
v___x_3653_ = lean_box(0);
lean_inc(v_levelParams_3651_);
v_levels_3654_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3651_, v___x_3653_);
v___x_3663_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3664_ = lean_array_get_size(v_infos_3640_);
v___x_3665_ = lean_nat_dec_lt(v___x_3647_, v___x_3664_);
if (v___x_3665_ == 0)
{
v___y_3656_ = v___x_3663_;
goto v___jp_3655_;
}
else
{
size_t v___x_3666_; size_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = ((size_t)0ULL);
v___x_3667_ = lean_usize_of_nat(v___x_3664_);
v___x_3668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3640_, v___x_3666_, v___x_3667_, v___x_3663_);
v___y_3656_ = v___x_3668_;
goto v___jp_3655_;
}
v___jp_3655_:
{
lean_object* v___f_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; lean_object* v___x_3662_; 
lean_inc_ref(v_infos_3640_);
v___f_3657_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3657_, 0, v_infos_3640_);
lean_closure_set(v___f_3657_, 1, v_levels_3654_);
lean_closure_set(v___f_3657_, 2, v___y_3656_);
v___x_3658_ = lean_array_get_size(v_infos_3640_);
lean_dec_ref(v_infos_3640_);
v___x_3659_ = lean_nat_sub(v_numParams_3650_, v___x_3658_);
lean_dec(v_numParams_3650_);
v___x_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
v___x_3661_ = 0;
v___x_3662_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_3652_, v___x_3660_, v___f_3657_, v___x_3661_, v___x_3661_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
return v___x_3662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_);
lean_dec(v_a_3673_);
lean_dec_ref(v_a_3672_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3676_, lean_object* v_constName_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3684_, lean_object* v_constName_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3684_, v_constName_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3692_, lean_object* v_ref_3693_, lean_object* v_constName_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3693_, v_constName_3694_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3701_, lean_object* v_ref_3702_, lean_object* v_constName_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3701_, v_ref_3702_, v_constName_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v_ref_3702_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3710_, lean_object* v_ref_3711_, lean_object* v_msg_3712_, lean_object* v_declHint_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; 
v___x_3719_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3711_, v_msg_3712_, v_declHint_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3720_, lean_object* v_ref_3721_, lean_object* v_msg_3722_, lean_object* v_declHint_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3720_, v_ref_3721_, v_msg_3722_, v_declHint_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v_ref_3721_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3730_, lean_object* v_declHint_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___x_3737_; 
v___x_3737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3730_, v_declHint_3731_, v___y_3735_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3738_, lean_object* v_declHint_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3738_, v_declHint_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3746_, lean_object* v_ref_3747_, lean_object* v_msg_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3747_, v_msg_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3755_, lean_object* v_ref_3756_, lean_object* v_msg_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3755_, v_ref_3756_, v_msg_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec(v___y_3759_);
lean_dec_ref(v___y_3758_);
lean_dec(v_ref_3756_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3767_, lean_object* v___x_3768_, lean_object* v_params_3769_, size_t v_sz_3770_, size_t v_i_3771_, lean_object* v_bs_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
uint8_t v___x_3778_; 
v___x_3778_ = lean_usize_dec_lt(v_i_3771_, v_sz_3770_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; 
lean_dec_ref(v_params_3769_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3767_);
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v_bs_3772_);
return v___x_3779_;
}
else
{
lean_object* v_v_3780_; lean_object* v_toConstantVal_3781_; lean_object* v_name_3782_; lean_object* v___x_3783_; lean_object* v_bs_x27_3784_; lean_object* v___y_3786_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_v_3780_ = lean_array_uget_borrowed(v_bs_3772_, v_i_3771_);
v_toConstantVal_3781_ = lean_ctor_get(v_v_3780_, 0);
v_name_3782_ = lean_ctor_get(v_toConstantVal_3781_, 0);
lean_inc(v_name_3782_);
v___x_3783_ = lean_unsigned_to_nat(0u);
v_bs_x27_3784_ = lean_array_uset(v_bs_3772_, v_i_3771_, v___x_3783_);
v___x_3800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3801_ = l_Lean_Name_append(v_name_3782_, v___x_3800_);
lean_inc(v___x_3767_);
v___x_3802_ = l_Lean_mkConst(v___x_3801_, v___x_3767_);
v___x_3803_ = l_Lean_Meta_unfoldDefinition(v___x_3802_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; size_t v_sz_3805_; size_t v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3803_, 1);
v_sz_3805_ = lean_array_size(v___x_3768_);
v___x_3806_ = ((size_t)0ULL);
lean_inc_ref(v___x_3768_);
v___x_3807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3769_, v_sz_3805_, v___x_3806_, v___x_3768_);
lean_inc_ref(v_params_3769_);
v___x_3808_ = l_Array_append___redArg(v_params_3769_, v___x_3807_);
lean_dec_ref(v___x_3807_);
v___x_3809_ = l_Lean_mkAppN(v_a_3804_, v___x_3808_);
lean_dec_ref(v___x_3808_);
v___x_3810_ = 0;
v___x_3811_ = 1;
v___x_3812_ = l_Lean_Meta_mkLambdaFVars(v_params_3769_, v___x_3809_, v___x_3810_, v___x_3778_, v___x_3810_, v___x_3778_, v___x_3811_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
v___y_3786_ = v___x_3812_;
goto v___jp_3785_;
}
else
{
v___y_3786_ = v___x_3803_;
goto v___jp_3785_;
}
v___jp_3785_:
{
if (lean_obj_tag(v___y_3786_) == 0)
{
lean_object* v_a_3787_; size_t v___x_3788_; size_t v___x_3789_; lean_object* v___x_3790_; 
v_a_3787_ = lean_ctor_get(v___y_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___y_3786_, 1);
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_add(v_i_3771_, v___x_3788_);
v___x_3790_ = lean_array_uset(v_bs_x27_3784_, v_i_3771_, v_a_3787_);
v_i_3771_ = v___x_3789_;
v_bs_3772_ = v___x_3790_;
goto _start;
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_dec_ref(v_bs_x27_3784_);
lean_dec_ref(v_params_3769_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3767_);
v_a_3792_ = lean_ctor_get(v___y_3786_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___y_3786_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___y_3786_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___y_3786_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3813_, lean_object* v___x_3814_, lean_object* v_params_3815_, lean_object* v_sz_3816_, lean_object* v_i_3817_, lean_object* v_bs_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
size_t v_sz_boxed_3824_; size_t v_i_boxed_3825_; lean_object* v_res_3826_; 
v_sz_boxed_3824_ = lean_unbox_usize(v_sz_3816_);
lean_dec(v_sz_3816_);
v_i_boxed_3825_ = lean_unbox_usize(v_i_3817_);
lean_dec(v_i_3817_);
v_res_3826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3813_, v___x_3814_, v_params_3815_, v_sz_boxed_3824_, v_i_boxed_3825_, v_bs_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3827_, lean_object* v___x_3828_, size_t v_sz_3829_, size_t v___x_3830_, lean_object* v_a_3831_, lean_object* v_params_3832_, lean_object* v_x_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3827_, v___x_3828_, v_params_3832_, v_sz_3829_, v___x_3830_, v_a_3831_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3842_, lean_object* v___x_3843_, lean_object* v_sz_3844_, lean_object* v___x_3845_, lean_object* v_a_3846_, lean_object* v_params_3847_, lean_object* v_x_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
size_t v_sz_boxed_3856_; size_t v___x_5749__boxed_3857_; lean_object* v_res_3858_; 
v_sz_boxed_3856_ = lean_unbox_usize(v_sz_3844_);
lean_dec(v_sz_3844_);
v___x_5749__boxed_3857_ = lean_unbox_usize(v___x_3845_);
lean_dec(v___x_3845_);
v_res_3858_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3842_, v___x_3843_, v_sz_boxed_3856_, v___x_5749__boxed_3857_, v_a_3846_, v_params_3847_, v_x_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec_ref(v_x_3848_);
return v_res_3858_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(lean_object* v___x_3859_, uint8_t v___x_3860_, lean_object* v_attr_3861_){
_start:
{
lean_object* v_name_3862_; lean_object* v___x_3863_; 
v_name_3862_ = lean_ctor_get(v_attr_3861_, 0);
lean_inc(v_name_3862_);
lean_dec_ref(v_attr_3861_);
v___x_3863_ = l_Lean_getAttributeImpl(v___x_3859_, v_name_3862_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_dec_ref_known(v___x_3863_, 1);
return v___x_3860_;
}
else
{
lean_object* v_a_3864_; lean_object* v_toAttributeImplCore_3865_; uint8_t v_applicationTime_3866_; uint8_t v___x_3867_; uint8_t v___x_3868_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref_known(v___x_3863_, 1);
v_toAttributeImplCore_3865_ = lean_ctor_get(v_a_3864_, 0);
lean_inc_ref(v_toAttributeImplCore_3865_);
lean_dec(v_a_3864_);
v_applicationTime_3866_ = lean_ctor_get_uint8(v_toAttributeImplCore_3865_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_3865_);
v___x_3867_ = 1;
v___x_3868_ = l_Lean_instBEqAttributeApplicationTime_beq(v_applicationTime_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
return v___x_3860_;
}
else
{
uint8_t v___x_3869_; 
v___x_3869_ = 0;
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed(lean_object* v___x_3870_, lean_object* v___x_3871_, lean_object* v_attr_3872_){
_start:
{
uint8_t v___x_5786__boxed_3873_; uint8_t v_res_3874_; lean_object* v_r_3875_; 
v___x_5786__boxed_3873_ = lean_unbox(v___x_3871_);
v_res_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(v___x_3870_, v___x_5786__boxed_3873_, v_attr_3872_);
v_r_3875_ = lean_box(v_res_3874_);
return v_r_3875_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = l_Lean_instInhabitedExpr;
v___x_3877_ = lean_box(0);
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
lean_ctor_set(v___x_3878_, 1, v___x_3876_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3879_, lean_object* v___x_3880_, lean_object* v_a_3881_, lean_object* v___x_3882_, size_t v_sz_3883_, size_t v_i_3884_, lean_object* v_bs_3885_){
_start:
{
uint8_t v___x_3886_; 
v___x_3886_ = lean_usize_dec_lt(v_i_3884_, v_sz_3883_);
if (v___x_3886_ == 0)
{
lean_dec(v___x_3882_);
lean_dec_ref(v___x_3880_);
return v_bs_3885_;
}
else
{
lean_object* v___x_3887_; lean_object* v_v_3888_; lean_object* v___x_3889_; lean_object* v_bs_x27_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v_modifiers_3893_; lean_object* v_ref_3894_; uint8_t v_isGreatest_3895_; lean_object* v_monotonicity_x3f_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3938_; 
v___x_3887_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v_v_3888_ = lean_array_uget(v_bs_3885_, v_i_3884_);
v___x_3889_ = lean_unsigned_to_nat(0u);
v_bs_x27_3890_ = lean_array_uset(v_bs_3885_, v_i_3884_, v___x_3889_);
v___x_3891_ = lean_usize_to_nat(v_i_3884_);
v___x_3892_ = lean_array_get(v___x_3887_, v_coinductiveElabData_3879_, v___x_3891_);
v_modifiers_3893_ = lean_ctor_get(v___x_3892_, 3);
v_ref_3894_ = lean_ctor_get(v___x_3892_, 2);
v_isGreatest_3895_ = lean_ctor_get_uint8(v___x_3892_, sizeof(void*)*6);
v_monotonicity_x3f_3896_ = lean_ctor_get(v___x_3892_, 5);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; lean_object* v_unused_3940_; lean_object* v_unused_3941_; 
v_unused_3939_ = lean_ctor_get(v___x_3892_, 4);
lean_dec(v_unused_3939_);
v_unused_3940_ = lean_ctor_get(v___x_3892_, 1);
lean_dec(v_unused_3940_);
v_unused_3941_ = lean_ctor_get(v___x_3892_, 0);
lean_dec(v_unused_3941_);
v___x_3898_ = v___x_3892_;
v_isShared_3899_ = v_isSharedCheck_3938_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_monotonicity_x3f_3896_);
lean_inc(v_modifiers_3893_);
lean_inc(v_ref_3894_);
lean_dec(v___x_3892_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3938_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v_stx_3900_; uint8_t v_visibility_3901_; uint8_t v_isProtected_3902_; uint8_t v_computeKind_3903_; uint8_t v_recKind_3904_; uint8_t v_isUnsafe_3905_; lean_object* v_attrs_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3936_; 
v_stx_3900_ = lean_ctor_get(v_modifiers_3893_, 0);
v_visibility_3901_ = lean_ctor_get_uint8(v_modifiers_3893_, sizeof(void*)*3);
v_isProtected_3902_ = lean_ctor_get_uint8(v_modifiers_3893_, sizeof(void*)*3 + 1);
v_computeKind_3903_ = lean_ctor_get_uint8(v_modifiers_3893_, sizeof(void*)*3 + 2);
v_recKind_3904_ = lean_ctor_get_uint8(v_modifiers_3893_, sizeof(void*)*3 + 3);
v_isUnsafe_3905_ = lean_ctor_get_uint8(v_modifiers_3893_, sizeof(void*)*3 + 4);
v_attrs_3906_ = lean_ctor_get(v_modifiers_3893_, 2);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_modifiers_3893_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v_modifiers_3893_, 1);
lean_dec(v_unused_3937_);
v___x_3908_ = v_modifiers_3893_;
v_isShared_3909_ = v_isSharedCheck_3936_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_attrs_3906_);
lean_inc(v_stx_3900_);
lean_dec(v_modifiers_3893_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3936_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v_fst_3912_; lean_object* v_snd_3913_; lean_object* v___x_3914_; lean_object* v___f_3915_; lean_object* v___x_3916_; lean_object* v___x_3918_; 
v___x_3910_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3911_ = lean_array_get_borrowed(v___x_3910_, v_a_3881_, v___x_3891_);
lean_dec(v___x_3891_);
v_fst_3912_ = lean_ctor_get(v___x_3911_, 0);
v_snd_3913_ = lean_ctor_get(v___x_3911_, 1);
v___x_3914_ = lean_box(v___x_3886_);
lean_inc_ref(v___x_3880_);
v___f_3915_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3915_, 0, v___x_3880_);
lean_closure_set(v___f_3915_, 1, v___x_3914_);
v___x_3916_ = lean_box(0);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 1, v___x_3916_);
v___x_3918_ = v___x_3908_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_stx_3900_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_attrs_3906_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*3, v_visibility_3901_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*3 + 1, v_isProtected_3902_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*3 + 2, v_computeKind_3903_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*3 + 3, v_recKind_3904_);
lean_ctor_set_uint8(v_reuseFailAlloc_3935_, sizeof(void*)*3 + 4, v_isUnsafe_3905_);
v___x_3918_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
lean_object* v___x_3919_; uint8_t v___x_3920_; uint8_t v___y_3922_; 
v___x_3919_ = l_Lean_Elab_Modifiers_filterAttrs(v___x_3918_, v___f_3915_);
v___x_3920_ = 0;
if (v_isGreatest_3895_ == 0)
{
uint8_t v___x_3933_; 
v___x_3933_ = 2;
v___y_3922_ = v___x_3933_;
goto v___jp_3921_;
}
else
{
uint8_t v___x_3934_; 
v___x_3934_ = 1;
v___y_3922_ = v___x_3934_;
goto v___jp_3921_;
}
v___jp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
lean_inc_n(v_ref_3894_, 2);
v___x_3923_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3923_, 0, v_ref_3894_);
lean_ctor_set(v___x_3923_, 1, v_monotonicity_x3f_3896_);
lean_ctor_set_uint8(v___x_3923_, sizeof(void*)*2, v___y_3922_);
v___x_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 5, v___x_3889_);
lean_ctor_set(v___x_3898_, 4, v___x_3916_);
lean_ctor_set(v___x_3898_, 3, v___x_3924_);
lean_ctor_set(v___x_3898_, 2, v___x_3916_);
lean_ctor_set(v___x_3898_, 1, v___x_3916_);
lean_ctor_set(v___x_3898_, 0, v_ref_3894_);
v___x_3926_ = v___x_3898_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_ref_3894_);
lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3932_, 2, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3932_, 3, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3932_, 4, v___x_3916_);
lean_ctor_set(v_reuseFailAlloc_3932_, 5, v___x_3889_);
v___x_3926_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
lean_object* v___x_3927_; size_t v___x_3928_; size_t v___x_3929_; lean_object* v___x_3930_; 
lean_ctor_set_uint8(v___x_3926_, sizeof(void*)*6, v___x_3886_);
lean_inc(v_snd_3913_);
lean_inc(v_fst_3912_);
lean_inc(v___x_3882_);
lean_inc(v_ref_3894_);
v___x_3927_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3927_, 0, v_ref_3894_);
lean_ctor_set(v___x_3927_, 1, v___x_3882_);
lean_ctor_set(v___x_3927_, 2, v___x_3919_);
lean_ctor_set(v___x_3927_, 3, v_fst_3912_);
lean_ctor_set(v___x_3927_, 4, v_ref_3894_);
lean_ctor_set(v___x_3927_, 5, v___x_3889_);
lean_ctor_set(v___x_3927_, 6, v_snd_3913_);
lean_ctor_set(v___x_3927_, 7, v_v_3888_);
lean_ctor_set(v___x_3927_, 8, v___x_3926_);
lean_ctor_set_uint8(v___x_3927_, sizeof(void*)*9, v___x_3920_);
v___x_3928_ = ((size_t)1ULL);
v___x_3929_ = lean_usize_add(v_i_3884_, v___x_3928_);
v___x_3930_ = lean_array_uset(v_bs_x27_3890_, v_i_3884_, v___x_3927_);
v_i_3884_ = v___x_3929_;
v_bs_3885_ = v___x_3930_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object* v_coinductiveElabData_3942_, lean_object* v___x_3943_, lean_object* v_a_3944_, lean_object* v___x_3945_, lean_object* v_sz_3946_, lean_object* v_i_3947_, lean_object* v_bs_3948_){
_start:
{
size_t v_sz_boxed_3949_; size_t v_i_boxed_3950_; lean_object* v_res_3951_; 
v_sz_boxed_3949_ = lean_unbox_usize(v_sz_3946_);
lean_dec(v_sz_3946_);
v_i_boxed_3950_ = lean_unbox_usize(v_i_3947_);
lean_dec(v_i_3947_);
v_res_3951_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_3942_, v___x_3943_, v_a_3944_, v___x_3945_, v_sz_boxed_3949_, v_i_boxed_3950_, v_bs_3948_);
lean_dec_ref(v_a_3944_);
lean_dec_ref(v_coinductiveElabData_3942_);
return v_res_3951_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0));
v___x_3954_ = l_Lean_stringToMessageData(v___x_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object* v_constName_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_){
_start:
{
lean_object* v___x_3963_; lean_object* v_env_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_st_ref_get(v___y_3961_);
v_env_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc_ref(v_env_3964_);
lean_dec(v___x_3963_);
lean_inc(v_constName_3955_);
v___x_3965_ = l_Lean_isInductiveCore_x3f(v_env_3964_, v_constName_3955_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v___x_3966_; uint8_t v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3966_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_3967_ = 0;
v___x_3968_ = l_Lean_MessageData_ofConstName(v_constName_3955_, v___x_3967_);
v___x_3969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3966_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3969_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_3971_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
return v___x_3972_;
}
else
{
lean_object* v_val_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec(v_constName_3955_);
v_val_3973_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3965_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_val_3973_);
lean_dec(v___x_3965_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
lean_ctor_set_tag(v___x_3975_, 0);
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_val_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object* v_constName_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t v_sz_3990_, size_t v_i_3991_, lean_object* v_bs_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
uint8_t v___x_4000_; 
v___x_4000_ = lean_usize_dec_lt(v_i_3991_, v_sz_3990_);
if (v___x_4000_ == 0)
{
lean_object* v___x_4001_; 
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v_bs_3992_);
return v___x_4001_;
}
else
{
lean_object* v_v_4002_; lean_object* v_declName_4003_; lean_object* v___x_4004_; lean_object* v_bs_x27_4005_; lean_object* v___x_4006_; 
v_v_4002_ = lean_array_uget_borrowed(v_bs_3992_, v_i_3991_);
v_declName_4003_ = lean_ctor_get(v_v_4002_, 1);
lean_inc(v_declName_4003_);
v___x_4004_ = lean_unsigned_to_nat(0u);
v_bs_x27_4005_ = lean_array_uset(v_bs_3992_, v_i_3991_, v___x_4004_);
v___x_4006_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_4003_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_object* v_a_4007_; size_t v___x_4008_; size_t v___x_4009_; lean_object* v___x_4010_; 
v_a_4007_ = lean_ctor_get(v___x_4006_, 0);
lean_inc(v_a_4007_);
lean_dec_ref_known(v___x_4006_, 1);
v___x_4008_ = ((size_t)1ULL);
v___x_4009_ = lean_usize_add(v_i_3991_, v___x_4008_);
v___x_4010_ = lean_array_uset(v_bs_x27_4005_, v_i_3991_, v_a_4007_);
v_i_3991_ = v___x_4009_;
v_bs_3992_ = v___x_4010_;
goto _start;
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec_ref(v_bs_x27_4005_);
v_a_4012_ = lean_ctor_get(v___x_4006_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4006_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4006_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4006_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object* v_sz_4020_, lean_object* v_i_4021_, lean_object* v_bs_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
size_t v_sz_boxed_4030_; size_t v_i_boxed_4031_; lean_object* v_res_4032_; 
v_sz_boxed_4030_ = lean_unbox_usize(v_sz_4020_);
lean_dec(v_sz_4020_);
v_i_boxed_4031_ = lean_unbox_usize(v_i_4021_);
lean_dec(v_i_4021_);
v_res_4032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_4030_, v_i_boxed_4031_, v_bs_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4024_);
lean_dec_ref(v___y_4023_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
if (lean_obj_tag(v_a_4033_) == 0)
{
lean_object* v___x_4035_; 
v___x_4035_ = l_List_reverse___redArg(v_a_4034_);
return v___x_4035_;
}
else
{
lean_object* v_head_4036_; lean_object* v_tail_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4046_; 
v_head_4036_ = lean_ctor_get(v_a_4033_, 0);
v_tail_4037_ = lean_ctor_get(v_a_4033_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_a_4033_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4039_ = v_a_4033_;
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_tail_4037_);
lean_inc(v_head_4036_);
lean_dec(v_a_4033_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4046_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4041_; lean_object* v___x_4043_; 
v___x_4041_ = l_Lean_MessageData_ofName(v_head_4036_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 1, v_a_4034_);
lean_ctor_set(v___x_4039_, 0, v___x_4041_);
v___x_4043_ = v___x_4039_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4041_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_a_4034_);
v___x_4043_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
v_a_4033_ = v_tail_4037_;
v_a_4034_ = v___x_4043_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t v_sz_4047_, size_t v_i_4048_, lean_object* v_bs_4049_){
_start:
{
uint8_t v___x_4050_; 
v___x_4050_ = lean_usize_dec_lt(v_i_4048_, v_sz_4047_);
if (v___x_4050_ == 0)
{
return v_bs_4049_;
}
else
{
lean_object* v_v_4051_; lean_object* v_declName_4052_; lean_object* v___x_4053_; lean_object* v_bs_x27_4054_; size_t v___x_4055_; size_t v___x_4056_; lean_object* v___x_4057_; 
v_v_4051_ = lean_array_uget_borrowed(v_bs_4049_, v_i_4048_);
v_declName_4052_ = lean_ctor_get(v_v_4051_, 1);
lean_inc(v_declName_4052_);
v___x_4053_ = lean_unsigned_to_nat(0u);
v_bs_x27_4054_ = lean_array_uset(v_bs_4049_, v_i_4048_, v___x_4053_);
v___x_4055_ = ((size_t)1ULL);
v___x_4056_ = lean_usize_add(v_i_4048_, v___x_4055_);
v___x_4057_ = lean_array_uset(v_bs_x27_4054_, v_i_4048_, v_declName_4052_);
v_i_4048_ = v___x_4056_;
v_bs_4049_ = v___x_4057_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object* v_sz_4059_, lean_object* v_i_4060_, lean_object* v_bs_4061_){
_start:
{
size_t v_sz_boxed_4062_; size_t v_i_boxed_4063_; lean_object* v_res_4064_; 
v_sz_boxed_4062_ = lean_unbox_usize(v_sz_4059_);
lean_dec(v_sz_4059_);
v_i_boxed_4063_ = lean_unbox_usize(v_i_4060_);
lean_dec(v_i_4060_);
v_res_4064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_4062_, v_i_boxed_4063_, v_bs_4061_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v_v_4065_, lean_object* v___x_4066_, lean_object* v___x_4067_, uint8_t v___x_4068_, lean_object* v_args_4069_, lean_object* v_body_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v_numParams_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; uint8_t v___x_4085_; uint8_t v___x_4086_; lean_object* v___x_4087_; 
v_numParams_4078_ = lean_ctor_get(v_v_4065_, 1);
lean_inc(v_numParams_4078_);
lean_dec(v_v_4065_);
lean_inc_ref(v_args_4069_);
v___x_4079_ = l_Array_toSubarray___redArg(v_args_4069_, v___x_4066_, v___x_4067_);
v___x_4080_ = l_Subarray_copy___redArg(v___x_4079_);
v___x_4081_ = lean_array_get_size(v_args_4069_);
v___x_4082_ = l_Array_toSubarray___redArg(v_args_4069_, v_numParams_4078_, v___x_4081_);
v___x_4083_ = l_Subarray_copy___redArg(v___x_4082_);
v___x_4084_ = l_Array_append___redArg(v___x_4080_, v___x_4083_);
lean_dec_ref(v___x_4083_);
v___x_4085_ = 0;
v___x_4086_ = 1;
v___x_4087_ = l_Lean_Meta_mkForallFVars(v___x_4084_, v_body_4070_, v___x_4085_, v___x_4068_, v___x_4068_, v___x_4086_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec_ref(v___x_4084_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v_v_4088_, lean_object* v___x_4089_, lean_object* v___x_4090_, lean_object* v___x_4091_, lean_object* v_args_4092_, lean_object* v_body_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
uint8_t v___x_6066__boxed_4101_; lean_object* v_res_4102_; 
v___x_6066__boxed_4101_ = lean_unbox(v___x_4091_);
v_res_4102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_4088_, v___x_4089_, v___x_4090_, v___x_6066__boxed_4101_, v_args_4092_, v_body_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_4103_, size_t v_sz_4104_, size_t v_i_4105_, lean_object* v_bs_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
uint8_t v___x_4114_; 
v___x_4114_ = lean_usize_dec_lt(v_i_4105_, v_sz_4104_);
if (v___x_4114_ == 0)
{
lean_object* v___x_4115_; 
lean_dec(v___x_4103_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v_bs_4106_);
return v___x_4115_;
}
else
{
lean_object* v_v_4116_; lean_object* v_toConstantVal_4117_; lean_object* v_name_4118_; lean_object* v_type_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___f_4122_; lean_object* v_bs_x27_4123_; uint8_t v___x_4124_; lean_object* v___x_4125_; 
v_v_4116_ = lean_array_uget_borrowed(v_bs_4106_, v_i_4105_);
v_toConstantVal_4117_ = lean_ctor_get(v_v_4116_, 0);
v_name_4118_ = lean_ctor_get(v_toConstantVal_4117_, 0);
lean_inc(v_name_4118_);
v_type_4119_ = lean_ctor_get(v_toConstantVal_4117_, 2);
lean_inc_ref(v_type_4119_);
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = lean_box(v___x_4114_);
lean_inc(v___x_4103_);
lean_inc(v_v_4116_);
v___f_4122_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4122_, 0, v_v_4116_);
lean_closure_set(v___f_4122_, 1, v___x_4120_);
lean_closure_set(v___f_4122_, 2, v___x_4103_);
lean_closure_set(v___f_4122_, 3, v___x_4121_);
v_bs_x27_4123_ = lean_array_uset(v_bs_4106_, v_i_4105_, v___x_4120_);
v___x_4124_ = 0;
v___x_4125_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4119_, v___f_4122_, v___x_4124_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; size_t v___x_4129_; size_t v___x_4130_; lean_object* v___x_4131_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v___x_4127_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4118_);
v___x_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set(v___x_4128_, 1, v_a_4126_);
v___x_4129_ = ((size_t)1ULL);
v___x_4130_ = lean_usize_add(v_i_4105_, v___x_4129_);
v___x_4131_ = lean_array_uset(v_bs_x27_4123_, v_i_4105_, v___x_4128_);
v_i_4105_ = v___x_4130_;
v_bs_4106_ = v___x_4131_;
goto _start;
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec_ref(v_bs_x27_4123_);
lean_dec(v_name_4118_);
lean_dec(v___x_4103_);
v_a_4133_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4125_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4125_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object* v___x_4141_, lean_object* v_sz_4142_, lean_object* v_i_4143_, lean_object* v_bs_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
size_t v_sz_boxed_4152_; size_t v_i_boxed_4153_; lean_object* v_res_4154_; 
v_sz_boxed_4152_ = lean_unbox_usize(v_sz_4142_);
lean_dec(v_sz_4142_);
v_i_boxed_4153_ = lean_unbox_usize(v_i_4143_);
lean_dec(v_i_4143_);
v_res_4154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4141_, v_sz_boxed_4152_, v_i_boxed_4153_, v_bs_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object* v___x_4155_, size_t v_sz_4156_, size_t v_i_4157_, lean_object* v_bs_4158_){
_start:
{
uint8_t v___x_4159_; 
v___x_4159_ = lean_usize_dec_lt(v_i_4157_, v_sz_4156_);
if (v___x_4159_ == 0)
{
lean_dec(v___x_4155_);
return v_bs_4158_;
}
else
{
lean_object* v_v_4160_; lean_object* v_fst_4161_; lean_object* v___x_4162_; lean_object* v_bs_x27_4163_; lean_object* v___x_4164_; size_t v___x_4165_; size_t v___x_4166_; lean_object* v___x_4167_; 
v_v_4160_ = lean_array_uget_borrowed(v_bs_4158_, v_i_4157_);
v_fst_4161_ = lean_ctor_get(v_v_4160_, 0);
lean_inc(v_fst_4161_);
v___x_4162_ = lean_unsigned_to_nat(0u);
v_bs_x27_4163_ = lean_array_uset(v_bs_4158_, v_i_4157_, v___x_4162_);
lean_inc(v___x_4155_);
v___x_4164_ = l_Lean_mkConst(v_fst_4161_, v___x_4155_);
v___x_4165_ = ((size_t)1ULL);
v___x_4166_ = lean_usize_add(v_i_4157_, v___x_4165_);
v___x_4167_ = lean_array_uset(v_bs_x27_4163_, v_i_4157_, v___x_4164_);
v_i_4157_ = v___x_4166_;
v_bs_4158_ = v___x_4167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object* v___x_4169_, lean_object* v_sz_4170_, lean_object* v_i_4171_, lean_object* v_bs_4172_){
_start:
{
size_t v_sz_boxed_4173_; size_t v_i_boxed_4174_; lean_object* v_res_4175_; 
v_sz_boxed_4173_ = lean_unbox_usize(v_sz_4170_);
lean_dec(v_sz_4170_);
v_i_boxed_4174_ = lean_unbox_usize(v_i_4171_);
lean_dec(v_i_4171_);
v_res_4175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4169_, v_sz_boxed_4173_, v_i_boxed_4174_, v_bs_4172_);
return v_res_4175_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCoinductive___closed__1(void){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = ((lean_object*)(l_Lean_Elab_Command_elabCoinductive___closed__0));
v___x_4178_ = l_Lean_stringToMessageData(v___x_4177_);
return v___x_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object* v_coinductiveElabData_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_toCold_4187_; lean_object* v_options_4188_; lean_object* v_inheritedTraceOptions_4189_; uint8_t v_hasTrace_4190_; lean_object* v___x_4191_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; 
v_toCold_4187_ = lean_ctor_get(v_a_4184_, 0);
v_options_4188_ = lean_ctor_get(v_toCold_4187_, 2);
v_inheritedTraceOptions_4189_ = lean_ctor_get(v_toCold_4187_, 11);
v_hasTrace_4190_ = lean_ctor_get_uint8(v_options_4188_, sizeof(void*)*1);
v___x_4191_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4190_ == 0)
{
v___y_4193_ = v_a_4180_;
v___y_4194_ = v_a_4181_;
v___y_4195_ = v_a_4182_;
v___y_4196_ = v_a_4183_;
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
goto v___jp_4192_;
}
else
{
lean_object* v_cls_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v_cls_4260_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4261_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4189_, v_options_4188_, v___x_4261_);
if (v___x_4262_ == 0)
{
v___y_4193_ = v_a_4180_;
v___y_4194_ = v_a_4181_;
v___y_4195_ = v_a_4182_;
v___y_4196_ = v_a_4183_;
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
goto v___jp_4192_;
}
else
{
lean_object* v___x_4263_; size_t v_sz_4264_; size_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4263_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4264_ = lean_array_size(v_coinductiveElabData_4179_);
v___x_4265_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4179_);
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4264_, v___x_4265_, v_coinductiveElabData_4179_);
v___x_4267_ = lean_array_to_list(v___x_4266_);
v___x_4268_ = lean_box(0);
v___x_4269_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4267_, v___x_4268_);
v___x_4270_ = l_Lean_MessageData_ofList(v___x_4269_);
v___x_4271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4263_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4260_, v___x_4271_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_dec_ref_known(v___x_4272_, 1);
v___y_4193_ = v_a_4180_;
v___y_4194_ = v_a_4181_;
v___y_4195_ = v_a_4182_;
v___y_4196_ = v_a_4183_;
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
goto v___jp_4192_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4179_);
return v___x_4272_;
}
}
}
v___jp_4192_:
{
size_t v_sz_4199_; size_t v___x_4200_; lean_object* v___x_4201_; 
v_sz_4199_ = lean_array_size(v_coinductiveElabData_4179_);
v___x_4200_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4179_);
v___x_4201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4199_, v___x_4200_, v_coinductiveElabData_4179_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v_toConstantVal_4205_; lean_object* v_numParams_4206_; lean_object* v_levelParams_4207_; lean_object* v_type_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; size_t v_sz_4213_; lean_object* v___x_4214_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc_n(v_a_4202_, 2);
lean_dec_ref_known(v___x_4201_, 1);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = lean_array_get_borrowed(v___x_4191_, v_a_4202_, v___x_4203_);
v_toConstantVal_4205_ = lean_ctor_get(v___x_4204_, 0);
v_numParams_4206_ = lean_ctor_get(v___x_4204_, 1);
v_levelParams_4207_ = lean_ctor_get(v_toConstantVal_4205_, 1);
v_type_4208_ = lean_ctor_get(v_toConstantVal_4205_, 2);
v___x_4209_ = lean_box(0);
lean_inc(v_levelParams_4207_);
v___x_4210_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4207_, v___x_4209_);
v___x_4211_ = lean_array_get_size(v_a_4202_);
v___x_4212_ = lean_nat_sub(v_numParams_4206_, v___x_4211_);
v_sz_4213_ = lean_array_size(v_a_4202_);
lean_inc(v___x_4212_);
v___x_4214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4212_, v_sz_4213_, v___x_4200_, v_a_4202_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; size_t v_sz_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___f_4220_; lean_object* v___x_4221_; uint8_t v___x_4222_; lean_object* v___x_4223_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc_n(v_a_4215_, 2);
lean_dec_ref_known(v___x_4214_, 1);
v_sz_4216_ = lean_array_size(v_a_4215_);
lean_inc(v___x_4210_);
v___x_4217_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4210_, v_sz_4216_, v___x_4200_, v_a_4215_);
v___x_4218_ = lean_box_usize(v_sz_4213_);
v___x_4219_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4202_);
v___f_4220_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4220_, 0, v___x_4210_);
lean_closure_set(v___f_4220_, 1, v___x_4217_);
lean_closure_set(v___f_4220_, 2, v___x_4218_);
lean_closure_set(v___f_4220_, 3, v___x_4219_);
lean_closure_set(v___f_4220_, 4, v_a_4202_);
lean_inc(v___x_4212_);
v___x_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4212_);
v___x_4222_ = 0;
lean_inc_ref(v_type_4208_);
v___x_4223_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4208_, v___x_4221_, v___f_4220_, v___x_4222_, v___x_4222_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4225_; lean_object* v_env_4226_; size_t v_sz_4227_; lean_object* v_lctx_4228_; lean_object* v_localInstances_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
lean_dec_ref_known(v___x_4223_, 1);
v___x_4225_ = lean_st_ref_get(v___y_4198_);
v_env_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc_ref(v_env_4226_);
lean_dec(v___x_4225_);
v_sz_4227_ = lean_array_size(v_a_4224_);
v_lctx_4228_ = lean_ctor_get(v___y_4195_, 2);
v_localInstances_4229_ = lean_ctor_get(v___y_4195_, 3);
lean_inc(v_levelParams_4207_);
v___x_4230_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4179_, v_env_4226_, v_a_4215_, v_levelParams_4207_, v_sz_4227_, v___x_4200_, v_a_4224_);
lean_dec(v_a_4215_);
lean_inc_ref(v_localInstances_4229_);
lean_inc_ref(v_lctx_4228_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v_lctx_4228_);
lean_ctor_set(v___x_4231_, 1, v_localInstances_4229_);
v___x_4232_ = l_Lean_Elab_partialFixpoint(v___x_4231_, v___x_4230_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v___x_4233_; 
lean_dec_ref_known(v___x_4232_, 1);
lean_inc(v_a_4202_);
v___x_4233_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4202_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4234_; 
lean_dec_ref_known(v___x_4233_, 1);
lean_inc(v_a_4202_);
v___x_4234_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4212_, v_a_4202_, v_coinductiveElabData_4179_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v___x_4235_; 
lean_dec_ref_known(v___x_4234_, 1);
v___x_4235_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4202_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
return v___x_4235_;
}
else
{
lean_dec(v_a_4202_);
return v___x_4234_;
}
}
else
{
lean_dec(v___x_4212_);
lean_dec(v_a_4202_);
lean_dec_ref(v_coinductiveElabData_4179_);
return v___x_4233_;
}
}
else
{
lean_dec(v___x_4212_);
lean_dec(v_a_4202_);
lean_dec_ref(v_coinductiveElabData_4179_);
return v___x_4232_;
}
}
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_a_4215_);
lean_dec(v___x_4212_);
lean_dec(v_a_4202_);
lean_dec_ref(v_coinductiveElabData_4179_);
v_a_4236_ = lean_ctor_get(v___x_4223_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4223_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4223_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4223_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec(v___x_4212_);
lean_dec(v___x_4210_);
lean_dec(v_a_4202_);
lean_dec_ref(v_coinductiveElabData_4179_);
v_a_4244_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4214_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4214_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec_ref(v_coinductiveElabData_4179_);
v_a_4252_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4201_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4201_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec_ref(v_a_4274_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v_params_4284_, size_t v_sz_4285_, size_t v_i_4286_, lean_object* v_bs_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4282_, v___x_4283_, v_params_4284_, v_sz_4285_, v_i_4286_, v_bs_4287_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4296_, lean_object* v___x_4297_, lean_object* v_params_4298_, lean_object* v_sz_4299_, lean_object* v_i_4300_, lean_object* v_bs_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
size_t v_sz_boxed_4309_; size_t v_i_boxed_4310_; lean_object* v_res_4311_; 
v_sz_boxed_4309_ = lean_unbox_usize(v_sz_4299_);
lean_dec(v_sz_4299_);
v_i_boxed_4310_ = lean_unbox_usize(v_i_4300_);
lean_dec(v_i_4300_);
v_res_4311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4296_, v___x_4297_, v_params_4298_, v_sz_boxed_4309_, v_i_boxed_4310_, v_bs_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4312_, lean_object* v___x_4313_, lean_object* v_a_4314_, lean_object* v___x_4315_, lean_object* v_as_4316_, size_t v_sz_4317_, size_t v_i_4318_, lean_object* v_bs_4319_){
_start:
{
lean_object* v___x_4320_; 
v___x_4320_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4312_, v___x_4313_, v_a_4314_, v___x_4315_, v_sz_4317_, v_i_4318_, v_bs_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4321_, lean_object* v___x_4322_, lean_object* v_a_4323_, lean_object* v___x_4324_, lean_object* v_as_4325_, lean_object* v_sz_4326_, lean_object* v_i_4327_, lean_object* v_bs_4328_){
_start:
{
size_t v_sz_boxed_4329_; size_t v_i_boxed_4330_; lean_object* v_res_4331_; 
v_sz_boxed_4329_ = lean_unbox_usize(v_sz_4326_);
lean_dec(v_sz_4326_);
v_i_boxed_4330_ = lean_unbox_usize(v_i_4327_);
lean_dec(v_i_4327_);
v_res_4331_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4321_, v___x_4322_, v_a_4323_, v___x_4324_, v_as_4325_, v_sz_boxed_4329_, v_i_boxed_4330_, v_bs_4328_);
lean_dec_ref(v_as_4325_);
lean_dec_ref(v_a_4323_);
lean_dec_ref(v_coinductiveElabData_4321_);
return v_res_4331_;
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
