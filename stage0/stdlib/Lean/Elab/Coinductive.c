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
size_t v_x_8833__boxed_500_; size_t v_x_8834__boxed_501_; lean_object* v_res_502_; 
v_x_8833__boxed_500_ = lean_unbox_usize(v_x_496_);
lean_dec(v_x_496_);
v_x_8834__boxed_501_ = lean_unbox_usize(v_x_497_);
lean_dec(v_x_497_);
v_res_502_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_495_, v_x_8833__boxed_500_, v_x_8834__boxed_501_, v_x_498_, v_x_499_);
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
lean_object* v___x_514_; lean_object* v_mctx_515_; lean_object* v_cache_516_; lean_object* v_zetaDeltaFVarIds_517_; lean_object* v_postponed_518_; lean_object* v_diag_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_548_; 
v___x_514_ = lean_st_ref_take(v___y_512_);
v_mctx_515_ = lean_ctor_get(v___x_514_, 0);
v_cache_516_ = lean_ctor_get(v___x_514_, 1);
v_zetaDeltaFVarIds_517_ = lean_ctor_get(v___x_514_, 2);
v_postponed_518_ = lean_ctor_get(v___x_514_, 3);
v_diag_519_ = lean_ctor_get(v___x_514_, 4);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_548_ == 0)
{
v___x_521_ = v___x_514_;
v_isShared_522_ = v_isSharedCheck_548_;
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
v_isShared_522_ = v_isSharedCheck_548_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v_depth_523_; lean_object* v_levelAssignDepth_524_; lean_object* v_lmvarCounter_525_; lean_object* v_mvarCounter_526_; lean_object* v_lDecls_527_; lean_object* v_decls_528_; lean_object* v_userNames_529_; lean_object* v_lAssignment_530_; lean_object* v_eAssignment_531_; lean_object* v_dAssignment_532_; lean_object* v_synthNormMemo_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_547_; 
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
v_synthNormMemo_533_ = lean_ctor_get(v_mctx_515_, 10);
v_isSharedCheck_547_ = !lean_is_exclusive(v_mctx_515_);
if (v_isSharedCheck_547_ == 0)
{
v___x_535_ = v_mctx_515_;
v_isShared_536_ = v_isSharedCheck_547_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_synthNormMemo_533_);
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
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_547_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_537_ = lean_box(0);
v___x_538_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_531_, v_mvarId_510_, v_val_511_);
if (v_isShared_536_ == 0)
{
lean_ctor_set(v___x_535_, 8, v___x_538_);
v___x_540_ = v___x_535_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_depth_523_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_levelAssignDepth_524_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_lmvarCounter_525_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_mvarCounter_526_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_lDecls_527_);
lean_ctor_set(v_reuseFailAlloc_546_, 5, v_decls_528_);
lean_ctor_set(v_reuseFailAlloc_546_, 6, v_userNames_529_);
lean_ctor_set(v_reuseFailAlloc_546_, 7, v_lAssignment_530_);
lean_ctor_set(v_reuseFailAlloc_546_, 8, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_546_, 9, v_dAssignment_532_);
lean_ctor_set(v_reuseFailAlloc_546_, 10, v_synthNormMemo_533_);
v___x_540_ = v_reuseFailAlloc_546_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_540_);
v___x_542_ = v___x_521_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_cache_516_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_zetaDeltaFVarIds_517_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_postponed_518_);
lean_ctor_set(v_reuseFailAlloc_545_, 4, v_diag_519_);
v___x_542_ = v_reuseFailAlloc_545_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_st_ref_put(v___y_512_, v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_537_);
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object* v_mvarId_549_, lean_object* v_val_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_549_, v_val_550_, v___y_551_);
lean_dec(v___y_551_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object* v_msgData_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_560_; lean_object* v_env_561_; uint8_t v___x_562_; lean_object* v_env_563_; lean_object* v___x_564_; lean_object* v_toCold_565_; lean_object* v_mctx_566_; lean_object* v_lctx_567_; lean_object* v_options_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_560_ = lean_st_ref_get(v___y_558_);
v_env_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc_ref(v_env_561_);
lean_dec(v___x_560_);
v___x_562_ = 0;
v_env_563_ = l_Lean_Environment_setRecordingDeps(v_env_561_, v___x_562_);
v___x_564_ = lean_st_ref_get(v___y_556_);
v_toCold_565_ = lean_ctor_get(v___y_557_, 0);
v_mctx_566_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_mctx_566_);
lean_dec(v___x_564_);
v_lctx_567_ = lean_ctor_get(v___y_555_, 2);
v_options_568_ = lean_ctor_get(v_toCold_565_, 2);
lean_inc_ref(v_options_568_);
lean_inc_ref(v_lctx_567_);
v___x_569_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_569_, 0, v_env_563_);
lean_ctor_set(v___x_569_, 1, v_mctx_566_);
lean_ctor_set(v___x_569_, 2, v_lctx_567_);
lean_ctor_set(v___x_569_, 3, v_options_568_);
v___x_570_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v_msgData_554_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_ref_585_; lean_object* v___x_586_; lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_595_; 
v_ref_585_ = lean_ctor_get(v___y_582_, 2);
v___x_586_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
v_a_587_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_595_ == 0)
{
v___x_589_ = v___x_586_;
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_586_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_595_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_inc(v_ref_585_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_ref_585_);
lean_ctor_set(v___x_591_, 1, v_a_587_);
if (v_isShared_590_ == 0)
{
lean_ctor_set_tag(v___x_589_, 1);
lean_ctor_set(v___x_589_, 0, v___x_591_);
v___x_593_ = v___x_589_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_603_, lean_object* v_b_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_array_610_; lean_object* v_start_611_; lean_object* v_stop_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_627_; 
v_array_610_ = lean_ctor_get(v_a_603_, 0);
v_start_611_ = lean_ctor_get(v_a_603_, 1);
v_stop_612_ = lean_ctor_get(v_a_603_, 2);
v_isSharedCheck_627_ = !lean_is_exclusive(v_a_603_);
if (v_isSharedCheck_627_ == 0)
{
v___x_614_ = v_a_603_;
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_stop_612_);
lean_inc(v_start_611_);
lean_inc(v_array_610_);
lean_dec(v_a_603_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_627_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_lt(v_start_611_, v_stop_612_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; 
lean_del_object(v___x_614_);
lean_dec(v_stop_612_);
lean_dec(v_start_611_);
lean_dec_ref(v_array_610_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_b_604_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_618_ = lean_unsigned_to_nat(1u);
v___x_619_ = lean_nat_add(v_start_611_, v___x_618_);
lean_inc_ref(v_array_610_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_619_);
v___x_621_ = v___x_614_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_array_610_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_stop_612_);
v___x_621_ = v_reuseFailAlloc_626_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_array_fget(v_array_610_, v_start_611_);
lean_dec(v_start_611_);
lean_dec_ref(v_array_610_);
v___x_623_ = l_Lean_Meta_mkCongrFun(v_b_604_, v___x_622_, v___y_605_, v___y_606_, v___y_607_, v___y_608_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v_a_603_ = v___x_621_;
v_b_604_ = v_a_624_;
goto _start;
}
else
{
lean_dec_ref(v___x_621_);
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_628_, v_b_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_636_, lean_object* v___x_637_, size_t v_sz_638_, size_t v_i_639_, lean_object* v_bs_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = lean_usize_dec_lt(v_i_639_, v_sz_638_);
if (v___x_641_ == 0)
{
lean_dec(v_levels_636_);
return v_bs_640_;
}
else
{
lean_object* v_v_642_; lean_object* v_toConstantVal_643_; lean_object* v_name_644_; lean_object* v___x_645_; lean_object* v_bs_x27_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v_v_642_ = lean_array_uget_borrowed(v_bs_640_, v_i_639_);
v_toConstantVal_643_ = lean_ctor_get(v_v_642_, 0);
v_name_644_ = lean_ctor_get(v_toConstantVal_643_, 0);
lean_inc(v_name_644_);
v___x_645_ = lean_unsigned_to_nat(0u);
v_bs_x27_646_ = lean_array_uset(v_bs_640_, v_i_639_, v___x_645_);
v___x_647_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_644_);
lean_inc(v_levels_636_);
v___x_648_ = l_Lean_mkConst(v___x_647_, v_levels_636_);
v___x_649_ = l_Lean_mkAppN(v___x_648_, v___x_637_);
v___x_650_ = ((size_t)1ULL);
v___x_651_ = lean_usize_add(v_i_639_, v___x_650_);
v___x_652_ = lean_array_uset(v_bs_x27_646_, v_i_639_, v___x_649_);
v_i_639_ = v___x_651_;
v_bs_640_ = v___x_652_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_654_, lean_object* v___x_655_, lean_object* v_sz_656_, lean_object* v_i_657_, lean_object* v_bs_658_){
_start:
{
size_t v_sz_boxed_659_; size_t v_i_boxed_660_; lean_object* v_res_661_; 
v_sz_boxed_659_ = lean_unbox_usize(v_sz_656_);
lean_dec(v_sz_656_);
v_i_boxed_660_ = lean_unbox_usize(v_i_657_);
lean_dec(v_i_657_);
v_res_661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_654_, v___x_655_, v_sz_boxed_659_, v_i_boxed_660_, v_bs_658_);
lean_dec_ref(v___x_655_);
return v_res_661_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0));
v___x_664_ = l_Lean_stringToMessageData(v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object* v_infos_668_, lean_object* v_numParams_669_, lean_object* v___x_670_, lean_object* v_name_671_, lean_object* v_levels_672_, lean_object* v_args_673_, lean_object* v_x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; size_t v_sz_698_; size_t v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_687_ = lean_array_get_size(v_infos_668_);
v___x_688_ = lean_nat_sub(v_numParams_669_, v___x_687_);
lean_inc(v___x_670_);
lean_inc_ref(v_args_673_);
v___x_689_ = l_Array_toSubarray___redArg(v_args_673_, v___x_670_, v___x_688_);
v___x_690_ = lean_array_get_size(v_args_673_);
v___x_691_ = l_Array_toSubarray___redArg(v_args_673_, v_numParams_669_, v___x_690_);
lean_inc_n(v_name_671_, 2);
v___x_692_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_671_);
lean_inc_n(v_levels_672_, 3);
lean_inc(v___x_692_);
v___x_693_ = l_Lean_mkConst(v___x_692_, v_levels_672_);
v___x_694_ = l_Subarray_copy___redArg(v___x_689_);
v___x_695_ = l_Lean_mkAppN(v___x_693_, v___x_694_);
lean_inc_ref(v___x_691_);
v___x_696_ = l_Subarray_copy___redArg(v___x_691_);
v___x_697_ = l_Lean_mkAppN(v___x_695_, v___x_696_);
v_sz_698_ = lean_array_size(v_infos_668_);
v___x_699_ = ((size_t)0ULL);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_672_, v___x_694_, v_sz_698_, v___x_699_, v_infos_668_);
v___x_701_ = l_Lean_mkConst(v_name_671_, v_levels_672_);
lean_inc_ref(v___x_694_);
v___x_702_ = l_Array_append___redArg(v___x_694_, v___x_700_);
lean_dec_ref(v___x_700_);
v___x_703_ = l_Array_append___redArg(v___x_702_, v___x_696_);
v___x_704_ = l_Lean_mkAppN(v___x_701_, v___x_703_);
lean_dec_ref(v___x_703_);
v___x_705_ = l_Lean_Meta_mkEq(v___x_697_, v___x_704_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_765_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_765_ == 0)
{
v___x_708_ = v___x_705_;
v_isShared_709_ = v_isSharedCheck_765_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_765_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set_tag(v___x_708_, 1);
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_764_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = 0;
v___x_713_ = lean_box(0);
v___x_714_ = l_Lean_Meta_mkFreshExprMVar(v___x_711_, v___x_712_, v___x_713_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = l_Lean_Expr_mvarId_x21(v_a_715_);
v___x_717_ = l_Lean_Meta_getEqnsFor_x3f(v___x_692_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
if (lean_obj_tag(v_a_718_) == 1)
{
lean_object* v_val_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_val_719_ = lean_ctor_get(v_a_718_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v_a_718_, 1);
v___x_720_ = lean_array_get_size(v_val_719_);
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_dec_eq(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec(v_val_719_);
lean_dec(v___x_716_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_691_);
lean_dec(v_levels_672_);
lean_dec(v_name_671_);
lean_dec(v___x_670_);
v___y_681_ = v___y_675_;
v___y_682_ = v___y_676_;
v___y_683_ = v___y_677_;
v___y_684_ = v___y_678_;
goto v___jp_680_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_723_ = lean_array_fget(v_val_719_, v___x_670_);
lean_dec(v___x_670_);
lean_dec(v_val_719_);
v___x_724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3));
v___x_725_ = l_Lean_Name_append(v_name_671_, v___x_724_);
lean_inc(v_levels_672_);
v___x_726_ = l_Lean_mkConst(v___x_725_, v_levels_672_);
v___x_727_ = l_Lean_mkConst(v___x_723_, v_levels_672_);
v___x_728_ = l_Lean_mkAppN(v___x_727_, v___x_694_);
v___x_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_691_, v___x_728_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; uint8_t v___x_731_; lean_object* v___x_732_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = 0;
v___x_732_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_716_, v___x_726_, v___x_731_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_733_, v_a_730_, v___y_676_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; 
lean_dec_ref_known(v___x_734_, 1);
v___x_735_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_715_, v___y_676_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Array_append___redArg(v___x_694_, v___x_696_);
lean_dec_ref(v___x_696_);
v___x_738_ = 1;
v___x_739_ = l_Lean_Meta_mkLambdaFVars(v___x_737_, v_a_736_, v___x_731_, v___x_722_, v___x_731_, v___x_722_, v___x_738_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec_ref(v___x_737_);
return v___x_739_;
}
else
{
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
return v___x_735_;
}
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_a_715_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
v_a_740_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_734_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_734_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_a_730_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
v_a_748_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_732_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_732_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_dec_ref(v___x_726_);
lean_dec(v___x_716_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
return v___x_729_;
}
}
}
else
{
lean_dec(v_a_718_);
lean_dec(v___x_716_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_691_);
lean_dec(v_levels_672_);
lean_dec(v_name_671_);
lean_dec(v___x_670_);
v___y_681_ = v___y_675_;
v___y_682_ = v___y_676_;
v___y_683_ = v___y_677_;
v___y_684_ = v___y_678_;
goto v___jp_680_;
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v___x_716_);
lean_dec(v_a_715_);
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
lean_dec_ref(v___x_691_);
lean_dec(v_levels_672_);
lean_dec(v_name_671_);
lean_dec(v___x_670_);
v_a_756_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_717_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_717_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
else
{
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
lean_dec(v___x_692_);
lean_dec_ref(v___x_691_);
lean_dec(v_levels_672_);
lean_dec(v_name_671_);
lean_dec(v___x_670_);
return v___x_714_;
}
}
}
}
else
{
lean_dec_ref(v___x_696_);
lean_dec_ref(v___x_694_);
lean_dec(v___x_692_);
lean_dec_ref(v___x_691_);
lean_dec(v_levels_672_);
lean_dec(v_name_671_);
lean_dec(v___x_670_);
return v___x_705_;
}
v___jp_680_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
v___x_686_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_685_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v___x_686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object* v_infos_766_, lean_object* v_numParams_767_, lean_object* v___x_768_, lean_object* v_name_769_, lean_object* v_levels_770_, lean_object* v_args_771_, lean_object* v_x_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_766_, v_numParams_767_, v___x_768_, v_name_769_, v_levels_770_, v_args_771_, v_x_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec_ref(v_x_772_);
return v_res_778_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0(void){
_start:
{
lean_object* v___x_779_; double v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_float_of_nat(v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_784_, lean_object* v_msg_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_ref_791_; lean_object* v___x_792_; lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_838_; 
v_ref_791_ = lean_ctor_get(v___y_788_, 2);
v___x_792_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
v_a_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_838_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_838_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_838_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_traceState_798_; lean_object* v_env_799_; lean_object* v_nextMacroScope_800_; lean_object* v_ngen_801_; lean_object* v_auxDeclNGen_802_; lean_object* v_cache_803_; lean_object* v_recordedDeps_804_; lean_object* v_messages_805_; lean_object* v_infoState_806_; lean_object* v_snapshotTasks_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_837_; 
v___x_797_ = lean_st_ref_take(v___y_789_);
v_traceState_798_ = lean_ctor_get(v___x_797_, 4);
v_env_799_ = lean_ctor_get(v___x_797_, 0);
v_nextMacroScope_800_ = lean_ctor_get(v___x_797_, 1);
v_ngen_801_ = lean_ctor_get(v___x_797_, 2);
v_auxDeclNGen_802_ = lean_ctor_get(v___x_797_, 3);
v_cache_803_ = lean_ctor_get(v___x_797_, 5);
v_recordedDeps_804_ = lean_ctor_get(v___x_797_, 6);
v_messages_805_ = lean_ctor_get(v___x_797_, 7);
v_infoState_806_ = lean_ctor_get(v___x_797_, 8);
v_snapshotTasks_807_ = lean_ctor_get(v___x_797_, 9);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_837_ == 0)
{
v___x_809_ = v___x_797_;
v_isShared_810_ = v_isSharedCheck_837_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_snapshotTasks_807_);
lean_inc(v_infoState_806_);
lean_inc(v_messages_805_);
lean_inc(v_recordedDeps_804_);
lean_inc(v_cache_803_);
lean_inc(v_traceState_798_);
lean_inc(v_auxDeclNGen_802_);
lean_inc(v_ngen_801_);
lean_inc(v_nextMacroScope_800_);
lean_inc(v_env_799_);
lean_dec(v___x_797_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_837_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
uint64_t v_tid_811_; lean_object* v_traces_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_836_; 
v_tid_811_ = lean_ctor_get_uint64(v_traceState_798_, sizeof(void*)*1);
v_traces_812_ = lean_ctor_get(v_traceState_798_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v_traceState_798_);
if (v_isSharedCheck_836_ == 0)
{
v___x_814_ = v_traceState_798_;
v_isShared_815_ = v_isSharedCheck_836_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_traces_812_);
lean_dec(v_traceState_798_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_836_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; double v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_816_ = lean_box(0);
v___x_817_ = lean_box(0);
v___x_818_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_819_ = 0;
v___x_820_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_821_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_821_, 0, v_cls_784_);
lean_ctor_set(v___x_821_, 1, v___x_817_);
lean_ctor_set(v___x_821_, 2, v___x_820_);
lean_ctor_set_float(v___x_821_, sizeof(void*)*3, v___x_818_);
lean_ctor_set_float(v___x_821_, sizeof(void*)*3 + 8, v___x_818_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*3 + 16, v___x_819_);
v___x_822_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_823_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v_a_793_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
lean_inc(v_ref_791_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_ref_791_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = l_Lean_PersistentArray_push___redArg(v_traces_812_, v___x_824_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_825_);
v___x_827_ = v___x_814_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_825_);
lean_ctor_set_uint64(v_reuseFailAlloc_835_, sizeof(void*)*1, v_tid_811_);
v___x_827_ = v_reuseFailAlloc_835_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_829_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 4, v___x_827_);
v___x_829_ = v___x_809_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_env_799_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_nextMacroScope_800_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_ngen_801_);
lean_ctor_set(v_reuseFailAlloc_834_, 3, v_auxDeclNGen_802_);
lean_ctor_set(v_reuseFailAlloc_834_, 4, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_834_, 5, v_cache_803_);
lean_ctor_set(v_reuseFailAlloc_834_, 6, v_recordedDeps_804_);
lean_ctor_set(v_reuseFailAlloc_834_, 7, v_messages_805_);
lean_ctor_set(v_reuseFailAlloc_834_, 8, v_infoState_806_);
lean_ctor_set(v_reuseFailAlloc_834_, 9, v_snapshotTasks_807_);
v___x_829_ = v_reuseFailAlloc_834_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_st_ref_put(v___y_789_, v___x_829_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_816_);
v___x_832_ = v___x_795_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_816_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object* v_cls_839_, lean_object* v_msg_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_839_, v_msg_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
return v_res_846_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_855_ = l_Lean_Name_append(v___x_854_, v___x_853_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5));
v___x_858_ = l_Lean_stringToMessageData(v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object* v_infos_859_, lean_object* v_levels_860_, lean_object* v_as_861_, size_t v_sz_862_, size_t v_i_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
uint8_t v___x_870_; 
v___x_870_ = lean_usize_dec_lt(v_i_863_, v_sz_862_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; 
lean_dec(v_levels_860_);
lean_dec_ref(v_infos_859_);
v___x_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_871_, 0, v_b_864_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v_toConstantVal_873_; lean_object* v_numParams_874_; lean_object* v_name_875_; lean_object* v_levelParams_876_; lean_object* v_type_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___f_880_; uint8_t v___x_881_; lean_object* v___x_882_; 
v_a_872_ = lean_array_uget_borrowed(v_as_861_, v_i_863_);
v_toConstantVal_873_ = lean_ctor_get(v_a_872_, 0);
v_numParams_874_ = lean_ctor_get(v_a_872_, 1);
v_name_875_ = lean_ctor_get(v_toConstantVal_873_, 0);
v_levelParams_876_ = lean_ctor_get(v_toConstantVal_873_, 1);
v_type_877_ = lean_ctor_get(v_toConstantVal_873_, 2);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_box(0);
lean_inc(v_levels_860_);
lean_inc(v_name_875_);
lean_inc(v_numParams_874_);
lean_inc_ref(v_infos_859_);
v___f_880_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed), 12, 5);
lean_closure_set(v___f_880_, 0, v_infos_859_);
lean_closure_set(v___f_880_, 1, v_numParams_874_);
lean_closure_set(v___f_880_, 2, v___x_878_);
lean_closure_set(v___f_880_, 3, v_name_875_);
lean_closure_set(v___f_880_, 4, v_levels_860_);
v___x_881_ = 0;
lean_inc_ref(v_type_877_);
v___x_882_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_877_, v___f_880_, v___x_881_, v___x_881_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v_toCold_918_; lean_object* v_options_919_; uint8_t v_hasTrace_920_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v_toCold_918_ = lean_ctor_get(v___y_867_, 0);
v_options_919_ = lean_ctor_get(v_toCold_918_, 2);
v_hasTrace_920_ = lean_ctor_get_uint8(v_options_919_, sizeof(void*)*1);
if (v_hasTrace_920_ == 0)
{
v___y_885_ = v___y_865_;
v___y_886_ = v___y_866_;
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
goto v___jp_884_;
}
else
{
lean_object* v_inheritedTraceOptions_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_inheritedTraceOptions_921_ = lean_ctor_get(v_toCold_918_, 11);
v___x_922_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_923_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_924_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_921_, v_options_919_, v___x_923_);
if (v___x_924_ == 0)
{
v___y_885_ = v___y_865_;
v___y_886_ = v___y_866_;
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
goto v___jp_884_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_925_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
lean_inc(v_a_883_);
v___x_926_ = l_Lean_MessageData_ofExpr(v_a_883_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_922_, v___x_927_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_dec_ref_known(v___x_928_, 1);
v___y_885_ = v___y_865_;
v___y_886_ = v___y_866_;
v___y_887_ = v___y_867_;
v___y_888_ = v___y_868_;
goto v___jp_884_;
}
else
{
lean_dec(v_a_883_);
lean_dec(v_levels_860_);
lean_dec_ref(v_infos_859_);
return v___x_928_;
}
}
}
v___jp_884_:
{
lean_object* v___x_889_; 
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
lean_inc(v_a_883_);
v___x_889_ = lean_infer_type(v_a_883_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
lean_inc(v_name_875_);
v___x_891_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_875_);
v___x_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_893_ = l_Lean_Name_append(v___x_891_, v___x_892_);
v___x_894_ = lean_box(0);
lean_inc(v_levelParams_876_);
v___x_895_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_893_, v_levelParams_876_, v_a_890_, v_a_883_, v___x_894_, v___y_888_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_a_896_);
v___x_898_ = l_Lean_addDecl(v___x_897_, v___x_881_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_898_) == 0)
{
size_t v___x_899_; size_t v___x_900_; 
lean_dec_ref_known(v___x_898_, 1);
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_863_, v___x_899_);
v_i_863_ = v___x_900_;
v_b_864_ = v___x_879_;
goto _start;
}
else
{
lean_dec(v_levels_860_);
lean_dec_ref(v_infos_859_);
return v___x_898_;
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_levels_860_);
lean_dec_ref(v_infos_859_);
v_a_902_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_895_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_895_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_a_883_);
lean_dec(v_levels_860_);
lean_dec_ref(v_infos_859_);
v_a_910_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_889_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_889_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_levels_860_);
lean_dec_ref(v_infos_859_);
v_a_929_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_882_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_882_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object* v_infos_937_, lean_object* v_levels_938_, lean_object* v_as_939_, lean_object* v_sz_940_, lean_object* v_i_941_, lean_object* v_b_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
size_t v_sz_boxed_948_; size_t v_i_boxed_949_; lean_object* v_res_950_; 
v_sz_boxed_948_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_949_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_937_, v_levels_938_, v_as_939_, v_sz_boxed_948_, v_i_boxed_949_, v_b_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec_ref(v_as_939_);
return v_res_950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object* v_infos_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_toConstantVal_960_; lean_object* v_levelParams_961_; lean_object* v___x_962_; lean_object* v_levels_963_; lean_object* v___x_964_; size_t v_sz_965_; size_t v___x_966_; lean_object* v___x_967_; 
v___x_957_ = l_Lean_instInhabitedInductiveVal_default;
v___x_958_ = lean_unsigned_to_nat(0u);
v___x_959_ = lean_array_get_borrowed(v___x_957_, v_infos_951_, v___x_958_);
v_toConstantVal_960_ = lean_ctor_get(v___x_959_, 0);
v_levelParams_961_ = lean_ctor_get(v_toConstantVal_960_, 1);
v___x_962_ = lean_box(0);
lean_inc(v_levelParams_961_);
v_levels_963_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_961_, v___x_962_);
v___x_964_ = lean_box(0);
v_sz_965_ = lean_array_size(v_infos_951_);
v___x_966_ = ((size_t)0ULL);
lean_inc_ref(v_infos_951_);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_951_, v_levels_963_, v_infos_951_, v_sz_965_, v___x_966_, v___x_964_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
lean_dec_ref(v_infos_951_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v___x_967_, 0);
lean_dec(v_unused_975_);
v___x_969_ = v___x_967_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_dec(v___x_967_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_964_);
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_964_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object* v_infos_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object* v_00_u03b1_983_, lean_object* v_msg_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object* v_00_u03b1_991_, lean_object* v_msg_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_991_, v_msg_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object* v_inst_999_, lean_object* v_R_1000_, lean_object* v_a_1001_, lean_object* v_b_1002_, lean_object* v_c_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_1001_, v_b_1002_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object* v_inst_1010_, lean_object* v_R_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_, lean_object* v_c_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_1010_, v_R_1011_, v_a_1012_, v_b_1013_, v_c_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object* v_mvarId_1021_, lean_object* v_val_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_1021_, v_val_1022_, v___y_1024_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object* v_mvarId_1029_, lean_object* v_val_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1029_, v_val_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object* v_00_u03b2_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_1038_, v_x_1039_, v_x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1042_, lean_object* v_x_1043_, size_t v_x_1044_, size_t v_x_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_1043_, v_x_1044_, v_x_1045_, v_x_1046_, v_x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
size_t v_x_9759__boxed_1055_; size_t v_x_9760__boxed_1056_; lean_object* v_res_1057_; 
v_x_9759__boxed_1055_ = lean_unbox_usize(v_x_1051_);
lean_dec(v_x_1051_);
v_x_9760__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_res_1057_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_1049_, v_x_1050_, v_x_9759__boxed_1055_, v_x_9760__boxed_1056_, v_x_1053_, v_x_1054_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1058_, lean_object* v_n_1059_, lean_object* v_k_1060_, lean_object* v_v_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v_n_1059_, v_k_1060_, v_v_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1063_, size_t v_depth_1064_, lean_object* v_keys_1065_, lean_object* v_vals_1066_, lean_object* v_heq_1067_, lean_object* v_i_1068_, lean_object* v_entries_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_1064_, v_keys_1065_, v_vals_1066_, v_i_1068_, v_entries_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1071_, lean_object* v_depth_1072_, lean_object* v_keys_1073_, lean_object* v_vals_1074_, lean_object* v_heq_1075_, lean_object* v_i_1076_, lean_object* v_entries_1077_){
_start:
{
size_t v_depth_boxed_1078_; lean_object* v_res_1079_; 
v_depth_boxed_1078_ = lean_unbox_usize(v_depth_1072_);
lean_dec(v_depth_1072_);
v_res_1079_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(v_00_u03b2_1071_, v_depth_boxed_1078_, v_keys_1073_, v_vals_1074_, v_heq_1075_, v_i_1076_, v_entries_1077_);
lean_dec_ref(v_vals_1074_);
lean_dec_ref(v_keys_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object* v_e_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_Expr_hasMVar(v_e_1086_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_e_1086_);
return v___x_1090_;
}
else
{
lean_object* v___x_1091_; lean_object* v_mctx_1092_; lean_object* v___x_1093_; lean_object* v_fst_1094_; lean_object* v_snd_1095_; lean_object* v___x_1096_; lean_object* v_cache_1097_; lean_object* v_zetaDeltaFVarIds_1098_; lean_object* v_postponed_1099_; lean_object* v_diag_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1109_; 
v___x_1091_ = lean_st_ref_get(v___y_1087_);
v_mctx_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc_ref(v_mctx_1092_);
lean_dec(v___x_1091_);
v___x_1093_ = l_Lean_instantiateMVarsCore(v_mctx_1092_, v_e_1086_);
v_fst_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_fst_1094_);
v_snd_1095_ = lean_ctor_get(v___x_1093_, 1);
lean_inc(v_snd_1095_);
lean_dec_ref(v___x_1093_);
v___x_1096_ = lean_st_ref_take(v___y_1087_);
v_cache_1097_ = lean_ctor_get(v___x_1096_, 1);
v_zetaDeltaFVarIds_1098_ = lean_ctor_get(v___x_1096_, 2);
v_postponed_1099_ = lean_ctor_get(v___x_1096_, 3);
v_diag_1100_ = lean_ctor_get(v___x_1096_, 4);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v___x_1096_, 0);
lean_dec(v_unused_1110_);
v___x_1102_ = v___x_1096_;
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_diag_1100_);
lean_inc(v_postponed_1099_);
lean_inc(v_zetaDeltaFVarIds_1098_);
lean_inc(v_cache_1097_);
lean_dec(v___x_1096_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1109_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v_snd_1095_);
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_snd_1095_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_cache_1097_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_zetaDeltaFVarIds_1098_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_postponed_1099_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_diag_1100_);
v___x_1105_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_st_ref_put(v___y_1087_, v___x_1105_);
v___x_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1107_, 0, v_fst_1094_);
return v___x_1107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_e_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1111_, v___y_1112_);
lean_dec(v___y_1112_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_e_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1115_, v___y_1119_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_e_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object* v_k_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v_b_1136_, lean_object* v_c_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v___x_1143_; 
lean_inc(v___y_1141_);
lean_inc_ref(v___y_1140_);
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
v___x_1143_ = lean_apply_9(v_k_1133_, v_b_1136_, v_c_1137_, v___y_1134_, v___y_1135_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, lean_box(0));
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object* v_k_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v_b_1147_, lean_object* v_c_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1144_, v___y_1145_, v___y_1146_, v_b_1147_, v_c_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_type_1155_, lean_object* v_k_1156_, uint8_t v_cleanupAnnotations_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___f_1165_; uint8_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1165_, 0, v_k_1156_);
lean_closure_set(v___f_1165_, 1, v___y_1158_);
lean_closure_set(v___f_1165_, 2, v___y_1159_);
v___x_1166_ = 0;
v___x_1167_ = lean_box(0);
v___x_1168_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1166_, v___x_1167_, v_type_1155_, v___f_1165_, v_cleanupAnnotations_1157_, v___x_1166_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
if (lean_obj_tag(v___x_1168_) == 0)
{
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_type_1177_, lean_object* v_k_1178_, lean_object* v_cleanupAnnotations_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1187_; lean_object* v_res_1188_; 
v_cleanupAnnotations_boxed_1187_ = lean_unbox(v_cleanupAnnotations_1179_);
v_res_1188_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1177_, v_k_1178_, v_cleanupAnnotations_boxed_1187_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_00_u03b1_1189_, lean_object* v_type_1190_, lean_object* v_k_1191_, uint8_t v_cleanupAnnotations_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1190_, v_k_1191_, v_cleanupAnnotations_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_00_u03b1_1201_, lean_object* v_type_1202_, lean_object* v_k_1203_, lean_object* v_cleanupAnnotations_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1212_; lean_object* v_res_1213_; 
v_cleanupAnnotations_boxed_1212_ = lean_unbox(v_cleanupAnnotations_1204_);
v_res_1213_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_1201_, v_type_1202_, v_k_1203_, v_cleanupAnnotations_boxed_1212_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_name_1214_, lean_object* v_levelParams_1215_, lean_object* v_type_1216_, lean_object* v_value_1217_, lean_object* v_hints_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; uint8_t v___y_1223_; lean_object* v_env_1231_; uint8_t v___x_1232_; 
v___x_1221_ = lean_st_ref_get(v___y_1219_);
v_env_1231_ = lean_ctor_get(v___x_1221_, 0);
lean_inc_ref_n(v_env_1231_, 2);
lean_dec(v___x_1221_);
v___x_1232_ = l_Lean_Environment_hasUnsafe(v_env_1231_, v_type_1216_);
if (v___x_1232_ == 0)
{
uint8_t v___x_1233_; 
v___x_1233_ = l_Lean_Environment_hasUnsafe(v_env_1231_, v_value_1217_);
if (v___x_1233_ == 0)
{
uint8_t v___x_1234_; 
v___x_1234_ = 1;
v___y_1223_ = v___x_1234_;
goto v___jp_1222_;
}
else
{
goto v___jp_1229_;
}
}
else
{
lean_dec_ref(v_env_1231_);
goto v___jp_1229_;
}
v___jp_1222_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
lean_inc(v_name_1214_);
v___x_1224_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1224_, 0, v_name_1214_);
lean_ctor_set(v___x_1224_, 1, v_levelParams_1215_);
lean_ctor_set(v___x_1224_, 2, v_type_1216_);
v___x_1225_ = lean_box(0);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v_name_1214_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1227_, 0, v___x_1224_);
lean_ctor_set(v___x_1227_, 1, v_value_1217_);
lean_ctor_set(v___x_1227_, 2, v_hints_1218_);
lean_ctor_set(v___x_1227_, 3, v___x_1226_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*4, v___y_1223_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v___x_1227_);
return v___x_1228_;
}
v___jp_1229_:
{
uint8_t v___x_1230_; 
v___x_1230_ = 0;
v___y_1223_ = v___x_1230_;
goto v___jp_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1235_, lean_object* v_levelParams_1236_, lean_object* v_type_1237_, lean_object* v_value_1238_, lean_object* v_hints_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1235_, v_levelParams_1236_, v_type_1237_, v_value_1238_, v_hints_1239_, v___y_1240_);
lean_dec(v___y_1240_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1243_, lean_object* v_levelParams_1244_, lean_object* v_type_1245_, lean_object* v_value_1246_, lean_object* v_hints_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1243_, v_levelParams_1244_, v_type_1245_, v_value_1246_, v_hints_1247_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1256_, lean_object* v_levelParams_1257_, lean_object* v_type_1258_, lean_object* v_value_1259_, lean_object* v_hints_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1256_, v_levelParams_1257_, v_type_1258_, v_value_1259_, v_hints_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1269_, lean_object* v_maxFVars_x3f_1270_, lean_object* v_k_1271_, uint8_t v_cleanupAnnotations_1272_, uint8_t v_whnfType_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___f_1281_; lean_object* v___x_1282_; 
lean_inc(v___y_1275_);
lean_inc_ref(v___y_1274_);
v___f_1281_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1281_, 0, v_k_1271_);
lean_closure_set(v___f_1281_, 1, v___y_1274_);
lean_closure_set(v___f_1281_, 2, v___y_1275_);
v___x_1282_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1269_, v_maxFVars_x3f_1270_, v___f_1281_, v_cleanupAnnotations_1272_, v_whnfType_1273_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
return v___x_1282_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
v_a_1283_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1282_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1282_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1291_, lean_object* v_maxFVars_x3f_1292_, lean_object* v_k_1293_, lean_object* v_cleanupAnnotations_1294_, lean_object* v_whnfType_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1303_; uint8_t v_whnfType_boxed_1304_; lean_object* v_res_1305_; 
v_cleanupAnnotations_boxed_1303_ = lean_unbox(v_cleanupAnnotations_1294_);
v_whnfType_boxed_1304_ = lean_unbox(v_whnfType_1295_);
v_res_1305_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1291_, v_maxFVars_x3f_1292_, v_k_1293_, v_cleanupAnnotations_boxed_1303_, v_whnfType_boxed_1304_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1306_, lean_object* v_type_1307_, lean_object* v_maxFVars_x3f_1308_, lean_object* v_k_1309_, uint8_t v_cleanupAnnotations_1310_, uint8_t v_whnfType_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1307_, v_maxFVars_x3f_1308_, v_k_1309_, v_cleanupAnnotations_1310_, v_whnfType_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1320_, lean_object* v_type_1321_, lean_object* v_maxFVars_x3f_1322_, lean_object* v_k_1323_, lean_object* v_cleanupAnnotations_1324_, lean_object* v_whnfType_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1333_; uint8_t v_whnfType_boxed_1334_; lean_object* v_res_1335_; 
v_cleanupAnnotations_boxed_1333_ = lean_unbox(v_cleanupAnnotations_1324_);
v_whnfType_boxed_1334_ = lean_unbox(v_whnfType_1325_);
v_res_1335_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1320_, v_type_1321_, v_maxFVars_x3f_1322_, v_k_1323_, v_cleanupAnnotations_boxed_1333_, v_whnfType_boxed_1334_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v_toCold_1344_; lean_object* v_options_1345_; uint8_t v_hasTrace_1346_; 
v_toCold_1344_ = lean_ctor_get(v___y_1341_, 0);
v_options_1345_ = lean_ctor_get(v_toCold_1344_, 2);
v_hasTrace_1346_ = lean_ctor_get_uint8(v_options_1345_, sizeof(void*)*1);
if (v_hasTrace_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec(v_cls_1336_);
v___x_1347_ = lean_box(v_hasTrace_1346_);
v___x_1348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
return v___x_1348_;
}
else
{
lean_object* v_inheritedTraceOptions_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_inheritedTraceOptions_1349_ = lean_ctor_get(v_toCold_1344_, 11);
v___x_1350_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1351_ = l_Lean_Name_append(v___x_1350_, v_cls_1336_);
v___x_1352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1349_, v_options_1345_, v___x_1351_);
lean_dec(v___x_1351_);
v___x_1353_ = lean_box(v___x_1352_);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object* v_cls_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_mvarId_1364_, lean_object* v_val_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; lean_object* v_mctx_1369_; lean_object* v_cache_1370_; lean_object* v_zetaDeltaFVarIds_1371_; lean_object* v_postponed_1372_; lean_object* v_diag_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1402_; 
v___x_1368_ = lean_st_ref_take(v___y_1366_);
v_mctx_1369_ = lean_ctor_get(v___x_1368_, 0);
v_cache_1370_ = lean_ctor_get(v___x_1368_, 1);
v_zetaDeltaFVarIds_1371_ = lean_ctor_get(v___x_1368_, 2);
v_postponed_1372_ = lean_ctor_get(v___x_1368_, 3);
v_diag_1373_ = lean_ctor_get(v___x_1368_, 4);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1375_ = v___x_1368_;
v_isShared_1376_ = v_isSharedCheck_1402_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_diag_1373_);
lean_inc(v_postponed_1372_);
lean_inc(v_zetaDeltaFVarIds_1371_);
lean_inc(v_cache_1370_);
lean_inc(v_mctx_1369_);
lean_dec(v___x_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1402_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v_depth_1377_; lean_object* v_levelAssignDepth_1378_; lean_object* v_lmvarCounter_1379_; lean_object* v_mvarCounter_1380_; lean_object* v_lDecls_1381_; lean_object* v_decls_1382_; lean_object* v_userNames_1383_; lean_object* v_lAssignment_1384_; lean_object* v_eAssignment_1385_; lean_object* v_dAssignment_1386_; lean_object* v_synthNormMemo_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1401_; 
v_depth_1377_ = lean_ctor_get(v_mctx_1369_, 0);
v_levelAssignDepth_1378_ = lean_ctor_get(v_mctx_1369_, 1);
v_lmvarCounter_1379_ = lean_ctor_get(v_mctx_1369_, 2);
v_mvarCounter_1380_ = lean_ctor_get(v_mctx_1369_, 3);
v_lDecls_1381_ = lean_ctor_get(v_mctx_1369_, 4);
v_decls_1382_ = lean_ctor_get(v_mctx_1369_, 5);
v_userNames_1383_ = lean_ctor_get(v_mctx_1369_, 6);
v_lAssignment_1384_ = lean_ctor_get(v_mctx_1369_, 7);
v_eAssignment_1385_ = lean_ctor_get(v_mctx_1369_, 8);
v_dAssignment_1386_ = lean_ctor_get(v_mctx_1369_, 9);
v_synthNormMemo_1387_ = lean_ctor_get(v_mctx_1369_, 10);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_mctx_1369_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1389_ = v_mctx_1369_;
v_isShared_1390_ = v_isSharedCheck_1401_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_synthNormMemo_1387_);
lean_inc(v_dAssignment_1386_);
lean_inc(v_eAssignment_1385_);
lean_inc(v_lAssignment_1384_);
lean_inc(v_userNames_1383_);
lean_inc(v_decls_1382_);
lean_inc(v_lDecls_1381_);
lean_inc(v_mvarCounter_1380_);
lean_inc(v_lmvarCounter_1379_);
lean_inc(v_levelAssignDepth_1378_);
lean_inc(v_depth_1377_);
lean_dec(v_mctx_1369_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1401_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1385_, v_mvarId_1364_, v_val_1365_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 8, v___x_1392_);
v___x_1394_ = v___x_1389_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_depth_1377_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_levelAssignDepth_1378_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_lmvarCounter_1379_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_mvarCounter_1380_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_lDecls_1381_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_decls_1382_);
lean_ctor_set(v_reuseFailAlloc_1400_, 6, v_userNames_1383_);
lean_ctor_set(v_reuseFailAlloc_1400_, 7, v_lAssignment_1384_);
lean_ctor_set(v_reuseFailAlloc_1400_, 8, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1400_, 9, v_dAssignment_1386_);
lean_ctor_set(v_reuseFailAlloc_1400_, 10, v_synthNormMemo_1387_);
v___x_1394_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1396_; 
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1394_);
v___x_1396_ = v___x_1375_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_cache_1370_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_zetaDeltaFVarIds_1371_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_postponed_1372_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_diag_1373_);
v___x_1396_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = lean_st_ref_put(v___y_1366_, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1391_);
return v___x_1398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_mvarId_1403_, lean_object* v_val_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1403_, v_val_1404_, v___y_1405_);
lean_dec(v___y_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_cls_1408_, lean_object* v_msg_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_ref_1415_; lean_object* v___x_1416_; lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1462_; 
v_ref_1415_ = lean_ctor_get(v___y_1412_, 2);
v___x_1416_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1419_ = v___x_1416_;
v_isShared_1420_ = v_isSharedCheck_1462_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1416_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1462_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v_traceState_1422_; lean_object* v_env_1423_; lean_object* v_nextMacroScope_1424_; lean_object* v_ngen_1425_; lean_object* v_auxDeclNGen_1426_; lean_object* v_cache_1427_; lean_object* v_recordedDeps_1428_; lean_object* v_messages_1429_; lean_object* v_infoState_1430_; lean_object* v_snapshotTasks_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1461_; 
v___x_1421_ = lean_st_ref_take(v___y_1413_);
v_traceState_1422_ = lean_ctor_get(v___x_1421_, 4);
v_env_1423_ = lean_ctor_get(v___x_1421_, 0);
v_nextMacroScope_1424_ = lean_ctor_get(v___x_1421_, 1);
v_ngen_1425_ = lean_ctor_get(v___x_1421_, 2);
v_auxDeclNGen_1426_ = lean_ctor_get(v___x_1421_, 3);
v_cache_1427_ = lean_ctor_get(v___x_1421_, 5);
v_recordedDeps_1428_ = lean_ctor_get(v___x_1421_, 6);
v_messages_1429_ = lean_ctor_get(v___x_1421_, 7);
v_infoState_1430_ = lean_ctor_get(v___x_1421_, 8);
v_snapshotTasks_1431_ = lean_ctor_get(v___x_1421_, 9);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1433_ = v___x_1421_;
v_isShared_1434_ = v_isSharedCheck_1461_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_snapshotTasks_1431_);
lean_inc(v_infoState_1430_);
lean_inc(v_messages_1429_);
lean_inc(v_recordedDeps_1428_);
lean_inc(v_cache_1427_);
lean_inc(v_traceState_1422_);
lean_inc(v_auxDeclNGen_1426_);
lean_inc(v_ngen_1425_);
lean_inc(v_nextMacroScope_1424_);
lean_inc(v_env_1423_);
lean_dec(v___x_1421_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1461_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
uint64_t v_tid_1435_; lean_object* v_traces_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1460_; 
v_tid_1435_ = lean_ctor_get_uint64(v_traceState_1422_, sizeof(void*)*1);
v_traces_1436_ = lean_ctor_get(v_traceState_1422_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_traceState_1422_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1438_ = v_traceState_1422_;
v_isShared_1439_ = v_isSharedCheck_1460_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_traces_1436_);
lean_dec(v_traceState_1422_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1460_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; double v___x_1442_; uint8_t v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_1443_ = 0;
v___x_1444_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_1445_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1445_, 0, v_cls_1408_);
lean_ctor_set(v___x_1445_, 1, v___x_1441_);
lean_ctor_set(v___x_1445_, 2, v___x_1444_);
lean_ctor_set_float(v___x_1445_, sizeof(void*)*3, v___x_1442_);
lean_ctor_set_float(v___x_1445_, sizeof(void*)*3 + 8, v___x_1442_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*3 + 16, v___x_1443_);
v___x_1446_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_1447_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v_a_1417_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
lean_inc(v_ref_1415_);
v___x_1448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1448_, 0, v_ref_1415_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
v___x_1449_ = l_Lean_PersistentArray_push___redArg(v_traces_1436_, v___x_1448_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1449_);
v___x_1451_ = v___x_1438_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1449_);
lean_ctor_set_uint64(v_reuseFailAlloc_1459_, sizeof(void*)*1, v_tid_1435_);
v___x_1451_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v___x_1451_);
v___x_1453_ = v___x_1433_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_env_1423_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_nextMacroScope_1424_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_ngen_1425_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_auxDeclNGen_1426_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1458_, 5, v_cache_1427_);
lean_ctor_set(v_reuseFailAlloc_1458_, 6, v_recordedDeps_1428_);
lean_ctor_set(v_reuseFailAlloc_1458_, 7, v_messages_1429_);
lean_ctor_set(v_reuseFailAlloc_1458_, 8, v_infoState_1430_);
lean_ctor_set(v_reuseFailAlloc_1458_, 9, v_snapshotTasks_1431_);
v___x_1453_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1454_ = lean_st_ref_put(v___y_1413_, v___x_1453_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1440_);
v___x_1456_ = v___x_1419_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1440_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_cls_1463_, lean_object* v_msg_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1463_, v_msg_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
return v_res_1470_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1471_; lean_object* v_dummy_1472_; 
v___x_1471_ = lean_box(0);
v_dummy_1472_ = l_Lean_Expr_sort___override(v___x_1471_);
return v_dummy_1472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1));
v___x_1475_ = l_Lean_stringToMessageData(v___x_1474_);
return v___x_1475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v_numParams_1479_, lean_object* v___x_1480_, lean_object* v_name_1481_, lean_object* v___x_1482_, lean_object* v___x_1483_, lean_object* v_name_1484_, lean_object* v___x_1485_, lean_object* v_cls_1486_, lean_object* v_fields_1487_, lean_object* v_bodyExpr_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_toCold_1496_; lean_object* v_options_1497_; lean_object* v_inheritedTraceOptions_1498_; uint8_t v_hasTrace_1499_; lean_object* v_nargs_1500_; lean_object* v_dummy_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; 
v_toCold_1496_ = lean_ctor_get(v___y_1493_, 0);
v_options_1497_ = lean_ctor_get(v_toCold_1496_, 2);
v_inheritedTraceOptions_1498_ = lean_ctor_get(v_toCold_1496_, 11);
v_hasTrace_1499_ = lean_ctor_get_uint8(v_options_1497_, sizeof(void*)*1);
v_nargs_1500_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1488_);
v_dummy_1501_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
lean_inc(v_nargs_1500_);
v___x_1502_ = lean_mk_array(v_nargs_1500_, v_dummy_1501_);
v___x_1503_ = lean_unsigned_to_nat(1u);
v___x_1504_ = lean_nat_sub(v_nargs_1500_, v___x_1503_);
lean_dec(v_nargs_1500_);
v___x_1505_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1488_, v___x_1502_, v___x_1504_);
v___x_1506_ = lean_array_get_size(v___x_1505_);
v___x_1507_ = lean_nat_add(v_numParams_1479_, v___x_1480_);
v___x_1508_ = l_Array_toSubarray___redArg(v___x_1505_, v___x_1507_, v___x_1506_);
v___x_1509_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1481_);
lean_inc(v___x_1482_);
lean_inc(v___x_1509_);
v___x_1510_ = l_Lean_mkConst(v___x_1509_, v___x_1482_);
v___x_1511_ = l_Lean_mkAppN(v___x_1510_, v___x_1483_);
v___x_1512_ = l_Subarray_copy___redArg(v___x_1508_);
v___x_1513_ = l_Lean_mkAppN(v___x_1511_, v___x_1512_);
lean_dec_ref(v___x_1512_);
if (v_hasTrace_1499_ == 0)
{
lean_dec(v_cls_1486_);
v___y_1515_ = v___y_1489_;
v___y_1516_ = v___y_1490_;
v___y_1517_ = v___y_1491_;
v___y_1518_ = v___y_1492_;
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
lean_inc(v_cls_1486_);
v___x_1570_ = l_Lean_Name_append(v___x_1569_, v_cls_1486_);
v___x_1571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1498_, v_options_1497_, v___x_1570_);
lean_dec(v___x_1570_);
if (v___x_1571_ == 0)
{
lean_dec(v_cls_1486_);
v___y_1515_ = v___y_1489_;
v___y_1516_ = v___y_1490_;
v___y_1517_ = v___y_1491_;
v___y_1518_ = v___y_1492_;
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
goto v___jp_1514_;
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1572_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
lean_inc(v_name_1484_);
v___x_1573_ = l_Lean_MessageData_ofName(v_name_1484_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
lean_inc_ref(v___x_1513_);
v___x_1577_ = l_Lean_MessageData_ofExpr(v___x_1513_);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1486_, v___x_1578_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_dec_ref_known(v___x_1579_, 1);
v___y_1515_ = v___y_1489_;
v___y_1516_ = v___y_1490_;
v___y_1517_ = v___y_1491_;
v___y_1518_ = v___y_1492_;
v___y_1519_ = v___y_1493_;
v___y_1520_ = v___y_1494_;
goto v___jp_1514_;
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v___x_1513_);
lean_dec(v___x_1509_);
lean_dec(v_name_1484_);
lean_dec(v___x_1482_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
v___jp_1514_:
{
lean_object* v___x_1521_; uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1513_);
v___x_1522_ = 0;
v___x_1523_ = lean_box(0);
v___x_1524_ = l_Lean_Meta_mkFreshExprMVar(v___x_1521_, v___x_1522_, v___x_1523_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = l_Lean_Expr_mvarId_x21(v_a_1525_);
v___x_1527_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1528_ = l_Lean_Name_append(v___x_1509_, v___x_1527_);
lean_inc(v___x_1482_);
v___x_1529_ = l_Lean_mkConst(v___x_1528_, v___x_1482_);
v___x_1530_ = l_Lean_mkAppN(v___x_1529_, v___x_1483_);
lean_inc(v___x_1526_);
v___x_1531_ = l_Lean_MVarId_getType(v___x_1526_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; uint8_t v___x_1533_; uint8_t v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v___x_1533_ = 0;
v___x_1534_ = 1;
v___x_1535_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1526_);
v___x_1536_ = l_Lean_MVarId_rewrite(v___x_1526_, v_a_1532_, v___x_1530_, v___x_1533_, v___x_1535_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v_eNew_1538_; lean_object* v_eqProof_1539_; lean_object* v___x_1540_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
v_eNew_1538_ = lean_ctor_get(v_a_1537_, 0);
lean_inc_ref(v_eNew_1538_);
v_eqProof_1539_ = lean_ctor_get(v_a_1537_, 1);
lean_inc_ref(v_eqProof_1539_);
lean_dec(v_a_1537_);
v___x_1540_ = l_Lean_MVarId_replaceTargetEq(v___x_1526_, v_eNew_1538_, v_eqProof_1539_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_a_1548_; uint8_t v___x_1549_; lean_object* v___x_1550_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v___x_1540_, 1);
v___x_1542_ = l_Lean_mkConst(v_name_1484_, v___x_1482_);
v___x_1543_ = l_Lean_mkAppN(v___x_1542_, v___x_1483_);
v___x_1544_ = l_Lean_mkAppN(v___x_1543_, v___x_1485_);
v___x_1545_ = l_Lean_mkAppN(v___x_1544_, v_fields_1487_);
v___x_1546_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_1541_, v___x_1545_, v___y_1518_);
lean_dec_ref(v___x_1546_);
v___x_1547_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1525_, v___y_1518_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = 1;
v___x_1550_ = l_Lean_Meta_mkLambdaFVars(v_fields_1487_, v_a_1548_, v___x_1533_, v___x_1534_, v___x_1533_, v___x_1534_, v___x_1549_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = l_Lean_Meta_mkLambdaFVars(v___x_1483_, v_a_1551_, v___x_1533_, v___x_1534_, v___x_1533_, v___x_1534_, v___x_1549_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v___x_1552_;
}
else
{
return v___x_1550_;
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_dec(v_a_1525_);
lean_dec(v_name_1484_);
lean_dec(v___x_1482_);
v_a_1553_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1540_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1540_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v___x_1526_);
lean_dec(v_a_1525_);
lean_dec(v_name_1484_);
lean_dec(v___x_1482_);
v_a_1561_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1536_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1536_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
else
{
lean_dec_ref(v___x_1530_);
lean_dec(v___x_1526_);
lean_dec(v_a_1525_);
lean_dec(v_name_1484_);
lean_dec(v___x_1482_);
return v___x_1531_;
}
}
else
{
lean_dec(v___x_1509_);
lean_dec(v_name_1484_);
lean_dec(v___x_1482_);
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_1588_ = _args[0];
lean_object* v___x_1589_ = _args[1];
lean_object* v_name_1590_ = _args[2];
lean_object* v___x_1591_ = _args[3];
lean_object* v___x_1592_ = _args[4];
lean_object* v_name_1593_ = _args[5];
lean_object* v___x_1594_ = _args[6];
lean_object* v_cls_1595_ = _args[7];
lean_object* v_fields_1596_ = _args[8];
lean_object* v_bodyExpr_1597_ = _args[9];
lean_object* v___y_1598_ = _args[10];
lean_object* v___y_1599_ = _args[11];
lean_object* v___y_1600_ = _args[12];
lean_object* v___y_1601_ = _args[13];
lean_object* v___y_1602_ = _args[14];
lean_object* v___y_1603_ = _args[15];
lean_object* v___y_1604_ = _args[16];
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1588_, v___x_1589_, v_name_1590_, v___x_1591_, v___x_1592_, v_name_1593_, v___x_1594_, v_cls_1595_, v_fields_1596_, v_bodyExpr_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v_fields_1596_);
lean_dec_ref(v___x_1594_);
lean_dec_ref(v___x_1592_);
lean_dec(v___x_1589_);
lean_dec(v_numParams_1588_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1606_, size_t v_sz_1607_, size_t v_i_1608_, lean_object* v_bs_1609_){
_start:
{
uint8_t v___x_1610_; 
v___x_1610_ = lean_usize_dec_lt(v_i_1608_, v_sz_1607_);
if (v___x_1610_ == 0)
{
return v_bs_1609_;
}
else
{
lean_object* v_v_1611_; lean_object* v___x_1612_; lean_object* v_bs_x27_1613_; lean_object* v___x_1614_; size_t v___x_1615_; size_t v___x_1616_; lean_object* v___x_1617_; 
v_v_1611_ = lean_array_uget(v_bs_1609_, v_i_1608_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v_bs_x27_1613_ = lean_array_uset(v_bs_1609_, v_i_1608_, v___x_1612_);
v___x_1614_ = l_Lean_mkAppN(v_v_1611_, v___x_1606_);
v___x_1615_ = ((size_t)1ULL);
v___x_1616_ = lean_usize_add(v_i_1608_, v___x_1615_);
v___x_1617_ = lean_array_uset(v_bs_x27_1613_, v_i_1608_, v___x_1614_);
v_i_1608_ = v___x_1616_;
v_bs_1609_ = v___x_1617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1619_, lean_object* v_sz_1620_, lean_object* v_i_1621_, lean_object* v_bs_1622_){
_start:
{
size_t v_sz_boxed_1623_; size_t v_i_boxed_1624_; lean_object* v_res_1625_; 
v_sz_boxed_1623_ = lean_unbox_usize(v_sz_1620_);
lean_dec(v_sz_1620_);
v_i_boxed_1624_ = lean_unbox_usize(v_i_1621_);
lean_dec(v_i_1621_);
v_res_1625_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1619_, v_sz_boxed_1623_, v_i_boxed_1624_, v_bs_1622_);
lean_dec_ref(v___x_1619_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1626_, size_t v_sz_1627_, size_t v_i_1628_, lean_object* v_bs_1629_){
_start:
{
uint8_t v___x_1630_; 
v___x_1630_ = lean_usize_dec_lt(v_i_1628_, v_sz_1627_);
if (v___x_1630_ == 0)
{
lean_dec(v___x_1626_);
return v_bs_1629_;
}
else
{
lean_object* v_v_1631_; lean_object* v___x_1632_; lean_object* v_bs_x27_1633_; lean_object* v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; lean_object* v___x_1637_; 
v_v_1631_ = lean_array_uget(v_bs_1629_, v_i_1628_);
v___x_1632_ = lean_unsigned_to_nat(0u);
v_bs_x27_1633_ = lean_array_uset(v_bs_1629_, v_i_1628_, v___x_1632_);
lean_inc(v___x_1626_);
v___x_1634_ = l_Lean_mkConst(v_v_1631_, v___x_1626_);
v___x_1635_ = ((size_t)1ULL);
v___x_1636_ = lean_usize_add(v_i_1628_, v___x_1635_);
v___x_1637_ = lean_array_uset(v_bs_x27_1633_, v_i_1628_, v___x_1634_);
v_i_1628_ = v___x_1636_;
v_bs_1629_ = v___x_1637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1639_, lean_object* v_sz_1640_, lean_object* v_i_1641_, lean_object* v_bs_1642_){
_start:
{
size_t v_sz_boxed_1643_; size_t v_i_boxed_1644_; lean_object* v_res_1645_; 
v_sz_boxed_1643_ = lean_unbox_usize(v_sz_1640_);
lean_dec(v_sz_1640_);
v_i_boxed_1644_ = lean_unbox_usize(v_i_1641_);
lean_dec(v_i_1641_);
v_res_1645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1639_, v_sz_boxed_1643_, v_i_boxed_1644_, v_bs_1642_);
return v_res_1645_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0));
v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object* v___x_1649_, lean_object* v_numParams_1650_, lean_object* v___x_1651_, lean_object* v___x_1652_, size_t v___x_1653_, lean_object* v___x_1654_, lean_object* v_name_1655_, lean_object* v_name_1656_, lean_object* v_cls_1657_, lean_object* v_levelParams_1658_, lean_object* v_ctorSyntax_1659_, lean_object* v___f_1660_, lean_object* v_args_1661_, lean_object* v_body_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; size_t v_sz_1673_; lean_object* v___x_1674_; size_t v_sz_1675_; lean_object* v___x_1676_; lean_object* v___f_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; uint8_t v___x_1680_; lean_object* v___x_1681_; 
lean_inc_n(v_numParams_1650_, 2);
v___x_1670_ = l_Array_extract___redArg(v_args_1661_, v___x_1649_, v_numParams_1650_);
v___x_1671_ = lean_array_get_size(v_args_1661_);
v___x_1672_ = l_Array_toSubarray___redArg(v_args_1661_, v_numParams_1650_, v___x_1671_);
v_sz_1673_ = lean_array_size(v___x_1651_);
lean_inc(v___x_1652_);
v___x_1674_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1652_, v_sz_1673_, v___x_1653_, v___x_1651_);
v_sz_1675_ = lean_array_size(v___x_1674_);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1670_, v_sz_1675_, v___x_1653_, v___x_1674_);
lean_inc(v_cls_1657_);
lean_inc_ref(v___x_1676_);
lean_inc(v_name_1656_);
v___f_1677_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1677_, 0, v_numParams_1650_);
lean_closure_set(v___f_1677_, 1, v___x_1654_);
lean_closure_set(v___f_1677_, 2, v_name_1655_);
lean_closure_set(v___f_1677_, 3, v___x_1652_);
lean_closure_set(v___f_1677_, 4, v___x_1670_);
lean_closure_set(v___f_1677_, 5, v_name_1656_);
lean_closure_set(v___f_1677_, 6, v___x_1676_);
lean_closure_set(v___f_1677_, 7, v_cls_1657_);
v___x_1678_ = l_Subarray_copy___redArg(v___x_1672_);
v___x_1679_ = l_Lean_Expr_replaceFVars(v_body_1662_, v___x_1678_, v___x_1676_);
lean_dec_ref(v___x_1676_);
lean_dec_ref(v___x_1678_);
v___x_1680_ = 0;
v___x_1681_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_1679_, v___f_1677_, v___x_1680_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1681_) == 0)
{
lean_object* v_a_1682_; lean_object* v___x_1683_; 
v_a_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc_n(v_a_1682_, 2);
lean_dec_ref_known(v___x_1681_, 1);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
v___x_1683_ = lean_infer_type(v_a_1682_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___y_1689_; lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___x_1708_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
lean_inc(v___y_1668_);
lean_inc_ref(v___y_1667_);
lean_inc(v___y_1666_);
lean_inc_ref(v___y_1665_);
lean_inc(v___y_1664_);
lean_inc_ref(v___y_1663_);
v___x_1708_ = lean_apply_7(v___f_1660_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, lean_box(0));
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; uint8_t v___x_1710_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref_known(v___x_1708_, 1);
v___x_1710_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
if (v___x_1710_ == 0)
{
lean_dec(v_cls_1657_);
v___y_1686_ = v___y_1663_;
v___y_1687_ = v___y_1664_;
v___y_1688_ = v___y_1665_;
v___y_1689_ = v___y_1666_;
v___y_1690_ = v___y_1667_;
v___y_1691_ = v___y_1668_;
goto v___jp_1685_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1711_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
lean_inc(v_a_1684_);
v___x_1712_ = l_Lean_MessageData_ofExpr(v_a_1684_);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1657_, v___x_1713_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_dec_ref_known(v___x_1714_, 1);
v___y_1686_ = v___y_1663_;
v___y_1687_ = v___y_1664_;
v___y_1688_ = v___y_1665_;
v___y_1689_ = v___y_1666_;
v___y_1690_ = v___y_1667_;
v___y_1691_ = v___y_1668_;
goto v___jp_1685_;
}
else
{
lean_dec(v_a_1684_);
lean_dec(v_a_1682_);
lean_dec(v_ctorSyntax_1659_);
lean_dec(v_levelParams_1658_);
lean_dec(v_name_1656_);
return v___x_1714_;
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_a_1684_);
lean_dec(v_a_1682_);
lean_dec(v_ctorSyntax_1659_);
lean_dec(v_levelParams_1658_);
lean_dec(v_cls_1657_);
lean_dec(v_name_1656_);
v_a_1715_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1708_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1708_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
v___jp_1685_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_a_1695_; lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1707_; 
v___x_1692_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1656_);
v___x_1693_ = lean_box(0);
lean_inc(v_a_1682_);
v___x_1694_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1692_, v_levelParams_1658_, v_a_1684_, v_a_1682_, v___x_1693_, v___y_1691_);
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1697_ = v___x_1694_;
v_isShared_1698_ = v_isSharedCheck_1707_;
goto v_resetjp_1696_;
}
else
{
lean_inc(v_a_1695_);
lean_dec(v___x_1694_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1707_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1700_; 
if (v_isShared_1698_ == 0)
{
lean_ctor_set_tag(v___x_1697_, 1);
v___x_1700_ = v___x_1697_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_a_1695_);
v___x_1700_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1701_; 
v___x_1701_ = l_Lean_addDecl(v___x_1700_, v___x_1680_, v___y_1690_, v___y_1691_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; 
lean_dec_ref_known(v___x_1701_, 1);
v___x_1702_ = lean_box(0);
v___x_1703_ = lean_box(0);
v___x_1704_ = 1;
v___x_1705_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1659_, v_a_1682_, v___x_1702_, v___x_1702_, v___x_1703_, v___x_1704_, v___x_1680_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
return v___x_1705_;
}
else
{
lean_dec(v_a_1682_);
lean_dec(v_ctorSyntax_1659_);
return v___x_1701_;
}
}
}
}
}
else
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1730_; 
lean_dec(v_a_1682_);
lean_dec_ref(v___f_1660_);
lean_dec(v_ctorSyntax_1659_);
lean_dec(v_levelParams_1658_);
lean_dec(v_cls_1657_);
lean_dec(v_name_1656_);
v_a_1723_ = lean_ctor_get(v___x_1683_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1683_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1725_ = v___x_1683_;
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1683_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1730_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1728_; 
if (v_isShared_1726_ == 0)
{
v___x_1728_ = v___x_1725_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_a_1723_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec_ref(v___f_1660_);
lean_dec(v_ctorSyntax_1659_);
lean_dec(v_levelParams_1658_);
lean_dec(v_cls_1657_);
lean_dec(v_name_1656_);
v_a_1731_ = lean_ctor_get(v___x_1681_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1681_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1681_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1681_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object** _args){
lean_object* v___x_1739_ = _args[0];
lean_object* v_numParams_1740_ = _args[1];
lean_object* v___x_1741_ = _args[2];
lean_object* v___x_1742_ = _args[3];
lean_object* v___x_1743_ = _args[4];
lean_object* v___x_1744_ = _args[5];
lean_object* v_name_1745_ = _args[6];
lean_object* v_name_1746_ = _args[7];
lean_object* v_cls_1747_ = _args[8];
lean_object* v_levelParams_1748_ = _args[9];
lean_object* v_ctorSyntax_1749_ = _args[10];
lean_object* v___f_1750_ = _args[11];
lean_object* v_args_1751_ = _args[12];
lean_object* v_body_1752_ = _args[13];
lean_object* v___y_1753_ = _args[14];
lean_object* v___y_1754_ = _args[15];
lean_object* v___y_1755_ = _args[16];
lean_object* v___y_1756_ = _args[17];
lean_object* v___y_1757_ = _args[18];
lean_object* v___y_1758_ = _args[19];
lean_object* v___y_1759_ = _args[20];
_start:
{
size_t v___x_8879__boxed_1760_; lean_object* v_res_1761_; 
v___x_8879__boxed_1760_ = lean_unbox_usize(v___x_1743_);
lean_dec(v___x_1743_);
v_res_1761_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1739_, v_numParams_1740_, v___x_1741_, v___x_1742_, v___x_8879__boxed_1760_, v___x_1744_, v_name_1745_, v_name_1746_, v_cls_1747_, v_levelParams_1748_, v_ctorSyntax_1749_, v___f_1750_, v_args_1751_, v_body_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec_ref(v_body_1752_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1762_, size_t v_i_1763_, lean_object* v_bs_1764_){
_start:
{
uint8_t v___x_1765_; 
v___x_1765_ = lean_usize_dec_lt(v_i_1763_, v_sz_1762_);
if (v___x_1765_ == 0)
{
return v_bs_1764_;
}
else
{
lean_object* v_v_1766_; lean_object* v_toConstantVal_1767_; lean_object* v_name_1768_; lean_object* v___x_1769_; lean_object* v_bs_x27_1770_; lean_object* v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v_v_1766_ = lean_array_uget_borrowed(v_bs_1764_, v_i_1763_);
v_toConstantVal_1767_ = lean_ctor_get(v_v_1766_, 0);
v_name_1768_ = lean_ctor_get(v_toConstantVal_1767_, 0);
lean_inc(v_name_1768_);
v___x_1769_ = lean_unsigned_to_nat(0u);
v_bs_x27_1770_ = lean_array_uset(v_bs_1764_, v_i_1763_, v___x_1769_);
v___x_1771_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1768_);
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_add(v_i_1763_, v___x_1772_);
v___x_1774_ = lean_array_uset(v_bs_x27_1770_, v_i_1763_, v___x_1771_);
v_i_1763_ = v___x_1773_;
v_bs_1764_ = v___x_1774_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1776_, lean_object* v_i_1777_, lean_object* v_bs_1778_){
_start:
{
size_t v_sz_boxed_1779_; size_t v_i_boxed_1780_; lean_object* v_res_1781_; 
v_sz_boxed_1779_ = lean_unbox_usize(v_sz_1776_);
lean_dec(v_sz_1776_);
v_i_boxed_1780_ = lean_unbox_usize(v_i_1777_);
lean_dec(v_i_1777_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1779_, v_i_boxed_1780_, v_bs_1778_);
return v_res_1781_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1));
v___x_1786_ = l_Lean_stringToMessageData(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1789_, lean_object* v_ctorSyntax_1790_, lean_object* v_numParams_1791_, lean_object* v_name_1792_, lean_object* v_ctor_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1801_; lean_object* v_cls_1802_; lean_object* v___f_1803_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___x_1831_; lean_object* v_a_1832_; uint8_t v___x_1833_; 
v___x_1801_ = l_Lean_instInhabitedInductiveVal_default;
v_cls_1802_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___f_1803_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1831_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1802_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
v___x_1833_ = lean_unbox(v_a_1832_);
lean_dec(v_a_1832_);
if (v___x_1833_ == 0)
{
v___y_1805_ = v_a_1794_;
v___y_1806_ = v_a_1795_;
v___y_1807_ = v_a_1796_;
v___y_1808_ = v_a_1797_;
v___y_1809_ = v_a_1798_;
v___y_1810_ = v_a_1799_;
goto v___jp_1804_;
}
else
{
lean_object* v_toConstantVal_1834_; lean_object* v_name_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_toConstantVal_1834_ = lean_ctor_get(v_ctor_1793_, 0);
v_name_1835_ = lean_ctor_get(v_toConstantVal_1834_, 0);
v___x_1836_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
lean_inc(v_name_1835_);
v___x_1837_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1835_);
v___x_1838_ = l_Lean_MessageData_ofName(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1836_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1802_, v___x_1839_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_dec_ref_known(v___x_1840_, 1);
v___y_1805_ = v_a_1794_;
v___y_1806_ = v_a_1795_;
v___y_1807_ = v_a_1796_;
v___y_1808_ = v_a_1797_;
v___y_1809_ = v_a_1798_;
v___y_1810_ = v_a_1799_;
goto v___jp_1804_;
}
else
{
lean_dec_ref(v_ctor_1793_);
lean_dec(v_name_1792_);
lean_dec(v_numParams_1791_);
lean_dec(v_ctorSyntax_1790_);
lean_dec_ref(v_infos_1789_);
return v___x_1840_;
}
}
v___jp_1804_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_toConstantVal_1813_; lean_object* v_toConstantVal_1814_; lean_object* v_levelParams_1815_; lean_object* v_name_1816_; lean_object* v_levelParams_1817_; lean_object* v_type_1818_; lean_object* v___x_1819_; size_t v_sz_1820_; size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; lean_object* v___x_1830_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_array_get_borrowed(v___x_1801_, v_infos_1789_, v___x_1811_);
v_toConstantVal_1813_ = lean_ctor_get(v___x_1812_, 0);
v_toConstantVal_1814_ = lean_ctor_get(v_ctor_1793_, 0);
lean_inc_ref(v_toConstantVal_1814_);
lean_dec_ref(v_ctor_1793_);
v_levelParams_1815_ = lean_ctor_get(v_toConstantVal_1813_, 1);
lean_inc(v_levelParams_1815_);
v_name_1816_ = lean_ctor_get(v_toConstantVal_1814_, 0);
lean_inc(v_name_1816_);
v_levelParams_1817_ = lean_ctor_get(v_toConstantVal_1814_, 1);
lean_inc(v_levelParams_1817_);
v_type_1818_ = lean_ctor_get(v_toConstantVal_1814_, 2);
lean_inc_ref(v_type_1818_);
lean_dec_ref(v_toConstantVal_1814_);
v___x_1819_ = lean_array_get_size(v_infos_1789_);
v_sz_1820_ = lean_array_size(v_infos_1789_);
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1820_, v___x_1821_, v_infos_1789_);
v___x_1823_ = lean_box(0);
v___x_1824_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1815_, v___x_1823_);
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1791_);
v___f_1826_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed), 21, 12);
lean_closure_set(v___f_1826_, 0, v___x_1811_);
lean_closure_set(v___f_1826_, 1, v_numParams_1791_);
lean_closure_set(v___f_1826_, 2, v___x_1822_);
lean_closure_set(v___f_1826_, 3, v___x_1824_);
lean_closure_set(v___f_1826_, 4, v___x_1825_);
lean_closure_set(v___f_1826_, 5, v___x_1819_);
lean_closure_set(v___f_1826_, 6, v_name_1792_);
lean_closure_set(v___f_1826_, 7, v_name_1816_);
lean_closure_set(v___f_1826_, 8, v_cls_1802_);
lean_closure_set(v___f_1826_, 9, v_levelParams_1817_);
lean_closure_set(v___f_1826_, 10, v_ctorSyntax_1790_);
lean_closure_set(v___f_1826_, 11, v___f_1803_);
v___x_1827_ = lean_nat_add(v_numParams_1791_, v___x_1819_);
lean_dec(v_numParams_1791_);
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
v___x_1829_ = 0;
v___x_1830_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1818_, v___x_1828_, v___f_1826_, v___x_1829_, v___x_1829_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1841_, lean_object* v_ctorSyntax_1842_, lean_object* v_numParams_1843_, lean_object* v_name_1844_, lean_object* v_ctor_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1841_, v_ctorSyntax_1842_, v_numParams_1843_, v_name_1844_, v_ctor_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_mvarId_1854_, lean_object* v_val_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1854_, v_val_1855_, v___y_1859_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_mvarId_1864_, lean_object* v_val_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1864_, v_val_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_cls_1874_, lean_object* v_msg_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1874_, v_msg_1875_, v___y_1878_, v___y_1879_, v___y_1880_, v___y_1881_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_cls_1884_, lean_object* v_msg_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1884_, v_msg_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v___y_1891_);
lean_dec_ref(v___y_1890_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1893_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_instMonadEIO___redArg();
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_toApplicative_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_2002_; 
v___x_1909_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1910_ = l_StateRefT_x27_instMonad___redArg(v___x_1909_);
v_toApplicative_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; 
v_unused_2003_ = lean_ctor_get(v___x_1910_, 1);
lean_dec(v_unused_2003_);
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_2002_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_toApplicative_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_2002_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_toFunctor_1915_; lean_object* v_toSeq_1916_; lean_object* v_toSeqLeft_1917_; lean_object* v_toSeqRight_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_2000_; 
v_toFunctor_1915_ = lean_ctor_get(v_toApplicative_1911_, 0);
v_toSeq_1916_ = lean_ctor_get(v_toApplicative_1911_, 2);
v_toSeqLeft_1917_ = lean_ctor_get(v_toApplicative_1911_, 3);
v_toSeqRight_1918_ = lean_ctor_get(v_toApplicative_1911_, 4);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_toApplicative_1911_);
if (v_isSharedCheck_2000_ == 0)
{
lean_object* v_unused_2001_; 
v_unused_2001_ = lean_ctor_get(v_toApplicative_1911_, 1);
lean_dec(v_unused_2001_);
v___x_1920_ = v_toApplicative_1911_;
v_isShared_1921_ = v_isSharedCheck_2000_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_toSeqRight_1918_);
lean_inc(v_toSeqLeft_1917_);
lean_inc(v_toSeq_1916_);
lean_inc(v_toFunctor_1915_);
lean_dec(v_toApplicative_1911_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_2000_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___x_1926_; lean_object* v___f_1927_; lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___x_1931_; 
v___f_1922_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1923_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1915_);
v___f_1924_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1924_, 0, v_toFunctor_1915_);
v___f_1925_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1925_, 0, v_toFunctor_1915_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___f_1924_);
lean_ctor_set(v___x_1926_, 1, v___f_1925_);
v___f_1927_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1927_, 0, v_toSeqRight_1918_);
v___f_1928_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1928_, 0, v_toSeqLeft_1917_);
v___f_1929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1929_, 0, v_toSeq_1916_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 4, v___f_1927_);
lean_ctor_set(v___x_1920_, 3, v___f_1928_);
lean_ctor_set(v___x_1920_, 2, v___f_1929_);
lean_ctor_set(v___x_1920_, 1, v___f_1922_);
lean_ctor_set(v___x_1920_, 0, v___x_1926_);
v___x_1931_ = v___x_1920_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___f_1922_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v___f_1929_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v___f_1928_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v___f_1927_);
v___x_1931_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v___f_1923_);
lean_ctor_set(v___x_1913_, 0, v___x_1931_);
v___x_1933_ = v___x_1913_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___f_1923_);
v___x_1933_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v_toApplicative_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1996_; 
v___x_1934_ = l_StateRefT_x27_instMonad___redArg(v___x_1933_);
v_toApplicative_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1934_, 1);
lean_dec(v_unused_1997_);
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1996_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_toApplicative_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1996_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_toFunctor_1939_; lean_object* v_toSeq_1940_; lean_object* v_toSeqLeft_1941_; lean_object* v_toSeqRight_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1994_; 
v_toFunctor_1939_ = lean_ctor_get(v_toApplicative_1935_, 0);
v_toSeq_1940_ = lean_ctor_get(v_toApplicative_1935_, 2);
v_toSeqLeft_1941_ = lean_ctor_get(v_toApplicative_1935_, 3);
v_toSeqRight_1942_ = lean_ctor_get(v_toApplicative_1935_, 4);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_toApplicative_1935_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v_toApplicative_1935_, 1);
lean_dec(v_unused_1995_);
v___x_1944_ = v_toApplicative_1935_;
v_isShared_1945_ = v_isSharedCheck_1994_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_toSeqRight_1942_);
lean_inc(v_toSeqLeft_1941_);
lean_inc(v_toSeq_1940_);
lean_inc(v_toFunctor_1939_);
lean_dec(v_toApplicative_1935_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1994_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___f_1946_; lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___x_1955_; 
v___f_1946_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1947_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1939_);
v___f_1948_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1948_, 0, v_toFunctor_1939_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toFunctor_1939_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___f_1948_);
lean_ctor_set(v___x_1950_, 1, v___f_1949_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toSeqRight_1942_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toSeqLeft_1941_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeq_1940_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___f_1951_);
lean_ctor_set(v___x_1944_, 3, v___f_1952_);
lean_ctor_set(v___x_1944_, 2, v___f_1953_);
lean_ctor_set(v___x_1944_, 1, v___f_1946_);
lean_ctor_set(v___x_1944_, 0, v___x_1950_);
v___x_1955_ = v___x_1944_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___f_1946_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v___f_1953_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v___f_1952_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v___f_1951_);
v___x_1955_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___f_1947_);
lean_ctor_set(v___x_1937_, 0, v___x_1955_);
v___x_1957_ = v___x_1937_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___f_1947_);
v___x_1957_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v_toApplicative_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1990_; 
v___x_1958_ = l_StateRefT_x27_instMonad___redArg(v___x_1957_);
v_toApplicative_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v___x_1958_, 1);
lean_dec(v_unused_1991_);
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1990_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_toApplicative_1959_);
lean_dec(v___x_1958_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1990_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_toFunctor_1963_; lean_object* v_toSeq_1964_; lean_object* v_toSeqLeft_1965_; lean_object* v_toSeqRight_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1988_; 
v_toFunctor_1963_ = lean_ctor_get(v_toApplicative_1959_, 0);
v_toSeq_1964_ = lean_ctor_get(v_toApplicative_1959_, 2);
v_toSeqLeft_1965_ = lean_ctor_get(v_toApplicative_1959_, 3);
v_toSeqRight_1966_ = lean_ctor_get(v_toApplicative_1959_, 4);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_toApplicative_1959_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v_toApplicative_1959_, 1);
lean_dec(v_unused_1989_);
v___x_1968_ = v_toApplicative_1959_;
v_isShared_1969_ = v_isSharedCheck_1988_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_toSeqRight_1966_);
lean_inc(v_toSeqLeft_1965_);
lean_inc(v_toSeq_1964_);
lean_inc(v_toFunctor_1963_);
lean_dec(v_toApplicative_1959_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1988_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___f_1970_; lean_object* v___f_1971_; lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___x_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___x_1979_; 
v___f_1970_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_1971_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1963_);
v___f_1972_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1972_, 0, v_toFunctor_1963_);
v___f_1973_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1973_, 0, v_toFunctor_1963_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___f_1972_);
lean_ctor_set(v___x_1974_, 1, v___f_1973_);
v___f_1975_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1975_, 0, v_toSeqRight_1966_);
v___f_1976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1976_, 0, v_toSeqLeft_1965_);
v___f_1977_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1977_, 0, v_toSeq_1964_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 4, v___f_1975_);
lean_ctor_set(v___x_1968_, 3, v___f_1976_);
lean_ctor_set(v___x_1968_, 2, v___f_1977_);
lean_ctor_set(v___x_1968_, 1, v___f_1970_);
lean_ctor_set(v___x_1968_, 0, v___x_1974_);
v___x_1979_ = v___x_1968_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___f_1970_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v___f_1977_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v___f_1976_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v___f_1975_);
v___x_1979_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1981_; 
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 1, v___f_1971_);
lean_ctor_set(v___x_1961_, 0, v___x_1979_);
v___x_1981_ = v___x_1961_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___f_1971_);
v___x_1981_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_3759__overap_1984_; lean_object* v___x_1985_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = l_instInhabitedOfMonad___redArg(v___x_1981_, v___x_1982_);
v___x_3759__overap_1984_ = lean_panic_fn_borrowed(v___x_1983_, v_msg_1901_);
lean_dec(v___x_1983_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
v___x_1985_ = lean_apply_7(v___x_3759__overap_1984_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, lean_box(0));
return v___x_1985_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2012_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2013_, lean_object* v_opt_2014_){
_start:
{
lean_object* v_name_2015_; lean_object* v_defValue_2016_; lean_object* v_map_2017_; lean_object* v___x_2018_; 
v_name_2015_ = lean_ctor_get(v_opt_2014_, 0);
v_defValue_2016_ = lean_ctor_get(v_opt_2014_, 1);
v_map_2017_ = lean_ctor_get(v_opts_2013_, 0);
v___x_2018_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2017_, v_name_2015_);
if (lean_obj_tag(v___x_2018_) == 0)
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_unbox(v_defValue_2016_);
return v___x_2019_;
}
else
{
lean_object* v_val_2020_; 
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_val_2020_);
lean_dec_ref_known(v___x_2018_, 1);
if (lean_obj_tag(v_val_2020_) == 1)
{
uint8_t v_v_2021_; 
v_v_2021_ = lean_ctor_get_uint8(v_val_2020_, 0);
lean_dec_ref_known(v_val_2020_, 0);
return v_v_2021_;
}
else
{
uint8_t v___x_2022_; 
lean_dec(v_val_2020_);
v___x_2022_ = lean_unbox(v_defValue_2016_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2023_, lean_object* v_opt_2024_){
_start:
{
uint8_t v_res_2025_; lean_object* v_r_2026_; 
v_res_2025_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2023_, v_opt_2024_);
lean_dec_ref(v_opt_2024_);
lean_dec_ref(v_opts_2023_);
v_r_2026_ = lean_box(v_res_2025_);
return v_r_2026_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; 
v___x_2027_ = lean_box(1);
v___x_2028_ = l_Lean_MessageData_ofFormat(v___x_2027_);
return v___x_2028_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2033_ = l_Lean_MessageData_ofFormat(v___x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
if (lean_obj_tag(v_x_2035_) == 0)
{
return v_x_2034_;
}
else
{
lean_object* v_head_2036_; lean_object* v_tail_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2059_; 
v_head_2036_ = lean_ctor_get(v_x_2035_, 0);
v_tail_2037_ = lean_ctor_get(v_x_2035_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_x_2035_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2039_ = v_x_2035_;
v_isShared_2040_ = v_isSharedCheck_2059_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_tail_2037_);
lean_inc(v_head_2036_);
lean_dec(v_x_2035_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2059_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v_before_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2057_; 
v_before_2041_ = lean_ctor_get(v_head_2036_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_head_2036_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_head_2036_, 1);
lean_dec(v_unused_2058_);
v___x_2043_ = v_head_2036_;
v_isShared_2044_ = v_isSharedCheck_2057_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_before_2041_);
lean_dec(v_head_2036_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2057_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 7);
lean_ctor_set(v___x_2043_, 1, v___x_2045_);
lean_ctor_set(v___x_2043_, 0, v_x_2034_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_x_2034_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2040_ == 0)
{
lean_ctor_set_tag(v___x_2039_, 7);
lean_ctor_set(v___x_2039_, 1, v___x_2048_);
lean_ctor_set(v___x_2039_, 0, v___x_2047_);
v___x_2050_ = v___x_2039_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = l_Lean_MessageData_ofSyntax(v_before_2041_);
v___x_2052_ = l_Lean_indentD(v___x_2051_);
v___x_2053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2050_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
v_x_2034_ = v___x_2053_;
v_x_2035_ = v_tail_2037_;
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
lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2063_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2064_ = l_Lean_MessageData_ofFormat(v___x_2063_);
return v___x_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2065_, lean_object* v_macroStack_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2069_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2067_);
v___x_2070_ = l_Lean_Elab_pp_macroStack;
v___x_2071_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v___x_2069_, v___x_2070_);
lean_dec_ref(v___x_2069_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v_macroStack_2066_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_msgData_2065_);
return v___x_2072_;
}
else
{
if (lean_obj_tag(v_macroStack_2066_) == 0)
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v_msgData_2065_);
return v___x_2073_;
}
else
{
lean_object* v_head_2074_; lean_object* v_after_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2090_; 
v_head_2074_ = lean_ctor_get(v_macroStack_2066_, 0);
lean_inc(v_head_2074_);
v_after_2075_ = lean_ctor_get(v_head_2074_, 1);
v_isSharedCheck_2090_ = !lean_is_exclusive(v_head_2074_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; 
v_unused_2091_ = lean_ctor_get(v_head_2074_, 0);
lean_dec(v_unused_2091_);
v___x_2077_ = v_head_2074_;
v_isShared_2078_ = v_isSharedCheck_2090_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_after_2075_);
lean_dec(v_head_2074_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2090_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 7);
lean_ctor_set(v___x_2077_, 1, v___x_2079_);
lean_ctor_set(v___x_2077_, 0, v_msgData_2065_);
v___x_2081_ = v___x_2077_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_msgData_2065_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v_msgData_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2082_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
v___x_2084_ = l_Lean_MessageData_ofSyntax(v_after_2075_);
v___x_2085_ = l_Lean_indentD(v___x_2084_);
v_msgData_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2086_, 0, v___x_2083_);
lean_ctor_set(v_msgData_2086_, 1, v___x_2085_);
v___x_2087_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2086_, v_macroStack_2066_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2092_, lean_object* v_macroStack_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2092_, v_macroStack_2093_, v___y_2094_);
lean_dec_ref(v___y_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_ref_2105_; lean_object* v_macroStack_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v___x_2110_; lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2119_; 
v_ref_2105_ = lean_ctor_get(v___y_2102_, 2);
v_macroStack_2106_ = lean_ctor_get(v___y_2098_, 1);
v___x_2107_ = l_Lean_Elab_getBetterRef(v_ref_2105_, v_macroStack_2106_);
v___x_2108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2097_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
lean_inc(v_macroStack_2106_);
v___x_2110_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2109_, v_macroStack_2106_, v___y_2102_);
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2113_ = v___x_2110_;
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2110_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2119_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2107_);
lean_ctor_set(v___x_2115_, 1, v_a_2111_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set_tag(v___x_2113_, 1);
lean_ctor_set(v___x_2113_, 0, v___x_2115_);
v___x_2117_ = v___x_2113_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2128_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2131_ = l_Lean_stringToMessageData(v___x_2130_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2138_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2139_ = lean_unsigned_to_nat(11u);
v___x_2140_ = lean_unsigned_to_nat(122u);
v___x_2141_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2142_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2143_ = l_mkPanicMessageWithDecl(v___x_2142_, v___x_2141_, v___x_2140_, v___x_2139_, v___x_2138_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2160_; lean_object* v_env_2161_; uint8_t v___x_2162_; lean_object* v___x_2163_; 
v___x_2160_ = lean_st_ref_get(v___y_2150_);
v_env_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc_ref(v_env_2161_);
lean_dec(v___x_2160_);
v___x_2162_ = 0;
lean_inc(v_constName_2144_);
v___x_2163_ = l_Lean_Environment_findAsync_x3f(v_env_2161_, v_constName_2144_, v___x_2162_);
if (lean_obj_tag(v___x_2163_) == 1)
{
lean_object* v_val_2164_; uint8_t v_kind_2165_; 
v_val_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_val_2164_);
lean_dec_ref_known(v___x_2163_, 1);
v_kind_2165_ = lean_ctor_get_uint8(v_val_2164_, sizeof(void*)*3);
if (v_kind_2165_ == 6)
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2164_);
if (lean_obj_tag(v___x_2166_) == 6)
{
lean_object* v_val_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_constName_2144_);
v_val_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_val_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set_tag(v___x_2169_, 0);
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_val_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v___x_2166_);
v___x_2175_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2176_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2175_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2185_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2185_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
if (lean_obj_tag(v_a_2177_) == 0)
{
lean_del_object(v___x_2179_);
goto v___jp_2152_;
}
else
{
lean_object* v_val_2181_; lean_object* v___x_2183_; 
lean_dec(v_constName_2144_);
v_val_2181_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v_a_2177_, 1);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v_val_2181_);
v___x_2183_ = v___x_2179_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_val_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_constName_2144_);
v_a_2186_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2176_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2176_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
else
{
lean_dec(v_val_2164_);
goto v___jp_2152_;
}
}
else
{
lean_dec(v___x_2163_);
goto v___jp_2152_;
}
v___jp_2152_:
{
lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2153_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2154_ = 0;
v___x_2155_ = l_Lean_MessageData_ofConstName(v_constName_2144_, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2153_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2158_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2203_, lean_object* v_infos_2204_, lean_object* v_numParams_2205_, lean_object* v_as_x27_2206_, lean_object* v_b_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
if (lean_obj_tag(v_as_x27_2206_) == 0)
{
lean_object* v___x_2215_; 
lean_dec(v_numParams_2205_);
lean_dec_ref(v_infos_2204_);
lean_dec_ref(v_a_2203_);
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v_b_2207_);
return v___x_2215_;
}
else
{
lean_object* v_head_2216_; lean_object* v_tail_2217_; lean_object* v_array_2218_; lean_object* v_start_2219_; lean_object* v_stop_2220_; uint8_t v___x_2221_; 
v_head_2216_ = lean_ctor_get(v_as_x27_2206_, 0);
v_tail_2217_ = lean_ctor_get(v_as_x27_2206_, 1);
v_array_2218_ = lean_ctor_get(v_b_2207_, 0);
v_start_2219_ = lean_ctor_get(v_b_2207_, 1);
v_stop_2220_ = lean_ctor_get(v_b_2207_, 2);
v___x_2221_ = lean_nat_dec_lt(v_start_2219_, v_stop_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec(v_numParams_2205_);
lean_dec_ref(v_infos_2204_);
lean_dec_ref(v_a_2203_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v_b_2207_);
return v___x_2222_;
}
else
{
lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2254_; 
lean_inc(v_stop_2220_);
lean_inc(v_start_2219_);
lean_inc_ref(v_array_2218_);
v_isSharedCheck_2254_ = !lean_is_exclusive(v_b_2207_);
if (v_isSharedCheck_2254_ == 0)
{
lean_object* v_unused_2255_; lean_object* v_unused_2256_; lean_object* v_unused_2257_; 
v_unused_2255_ = lean_ctor_get(v_b_2207_, 2);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_b_2207_, 1);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_b_2207_, 0);
lean_dec(v_unused_2257_);
v___x_2224_ = v_b_2207_;
v_isShared_2225_ = v_isSharedCheck_2254_;
goto v_resetjp_2223_;
}
else
{
lean_dec(v_b_2207_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2254_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2226_ = lean_array_fget(v_array_2218_, v_start_2219_);
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_nat_add(v_start_2219_, v___x_2227_);
lean_dec(v_start_2219_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 1, v___x_2228_);
v___x_2230_ = v___x_2224_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_array_2218_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v_stop_2220_);
v___x_2230_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; 
lean_inc(v_head_2216_);
v___x_2231_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2216_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_toConstantVal_2232_; lean_object* v_a_2233_; lean_object* v_name_2234_; lean_object* v___x_2235_; 
v_toConstantVal_2232_ = lean_ctor_get(v_a_2203_, 0);
v_a_2233_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2231_, 1);
v_name_2234_ = lean_ctor_get(v_toConstantVal_2232_, 0);
lean_inc(v_name_2234_);
lean_inc(v_numParams_2205_);
lean_inc_ref(v_infos_2204_);
v___x_2235_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2204_, v___x_2226_, v_numParams_2205_, v_name_2234_, v_a_2233_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_dec_ref_known(v___x_2235_, 1);
v_as_x27_2206_ = v_tail_2217_;
v_b_2207_ = v___x_2230_;
goto _start;
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_dec_ref(v___x_2230_);
lean_dec(v_numParams_2205_);
lean_dec_ref(v_infos_2204_);
lean_dec_ref(v_a_2203_);
v_a_2237_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2235_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2235_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec_ref(v___x_2230_);
lean_dec(v___x_2226_);
lean_dec(v_numParams_2205_);
lean_dec_ref(v_infos_2204_);
lean_dec_ref(v_a_2203_);
v_a_2245_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2231_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2231_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2258_, lean_object* v_infos_2259_, lean_object* v_numParams_2260_, lean_object* v_as_x27_2261_, lean_object* v_b_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2258_, v_infos_2259_, v_numParams_2260_, v_as_x27_2261_, v_b_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v_as_x27_2261_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2271_, lean_object* v_numParams_2272_, lean_object* v_as_2273_, size_t v_sz_2274_, size_t v_i_2275_, lean_object* v_b_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
uint8_t v___x_2284_; 
v___x_2284_ = lean_usize_dec_lt(v_i_2275_, v_sz_2274_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; 
lean_dec(v_numParams_2272_);
lean_dec_ref(v_infos_2271_);
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v_b_2276_);
return v___x_2285_;
}
else
{
lean_object* v_array_2286_; lean_object* v_start_2287_; lean_object* v_stop_2288_; uint8_t v___x_2289_; 
v_array_2286_ = lean_ctor_get(v_b_2276_, 0);
v_start_2287_ = lean_ctor_get(v_b_2276_, 1);
v_stop_2288_ = lean_ctor_get(v_b_2276_, 2);
v___x_2289_ = lean_nat_dec_lt(v_start_2287_, v_stop_2288_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_dec(v_numParams_2272_);
lean_dec_ref(v_infos_2271_);
v___x_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2290_, 0, v_b_2276_);
return v___x_2290_;
}
else
{
lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2318_; 
lean_inc(v_stop_2288_);
lean_inc(v_start_2287_);
lean_inc_ref(v_array_2286_);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_b_2276_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; lean_object* v_unused_2320_; lean_object* v_unused_2321_; 
v_unused_2319_ = lean_ctor_get(v_b_2276_, 2);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v_b_2276_, 1);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_b_2276_, 0);
lean_dec(v_unused_2321_);
v___x_2292_ = v_b_2276_;
v_isShared_2293_ = v_isSharedCheck_2318_;
goto v_resetjp_2291_;
}
else
{
lean_dec(v_b_2276_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2318_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2294_; lean_object* v_ctorSyntax_2295_; lean_object* v_a_2296_; lean_object* v_ctors_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2294_ = lean_array_fget_borrowed(v_array_2286_, v_start_2287_);
v_ctorSyntax_2295_ = lean_ctor_get(v___x_2294_, 4);
lean_inc_ref(v_ctorSyntax_2295_);
v_a_2296_ = lean_array_uget_borrowed(v_as_2273_, v_i_2275_);
v_ctors_2297_ = lean_ctor_get(v_a_2296_, 4);
v___x_2298_ = lean_array_get_size(v_ctorSyntax_2295_);
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_nat_add(v_start_2287_, v___x_2299_);
lean_dec(v_start_2287_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___x_2300_);
v___x_2302_ = v___x_2292_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_array_2286_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_stop_2288_);
v___x_2302_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = l_Array_toSubarray___redArg(v_ctorSyntax_2295_, v___x_2303_, v___x_2298_);
lean_inc(v_numParams_2272_);
lean_inc_ref(v_infos_2271_);
lean_inc(v_a_2296_);
v___x_2305_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2296_, v_infos_2271_, v_numParams_2272_, v_ctors_2297_, v___x_2304_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
if (lean_obj_tag(v___x_2305_) == 0)
{
size_t v___x_2306_; size_t v___x_2307_; 
lean_dec_ref_known(v___x_2305_, 1);
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = lean_usize_add(v_i_2275_, v___x_2306_);
v_i_2275_ = v___x_2307_;
v_b_2276_ = v___x_2302_;
goto _start;
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v___x_2302_);
lean_dec(v_numParams_2272_);
lean_dec_ref(v_infos_2271_);
v_a_2309_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2305_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2305_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2322_, lean_object* v_numParams_2323_, lean_object* v_as_2324_, lean_object* v_sz_2325_, lean_object* v_i_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
size_t v_sz_boxed_2335_; size_t v_i_boxed_2336_; lean_object* v_res_2337_; 
v_sz_boxed_2335_ = lean_unbox_usize(v_sz_2325_);
lean_dec(v_sz_2325_);
v_i_boxed_2336_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_res_2337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2322_, v_numParams_2323_, v_as_2324_, v_sz_boxed_2335_, v_i_boxed_2336_, v_b_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec_ref(v_as_2324_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2338_, lean_object* v_infos_2339_, lean_object* v_coinductiveElabData_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; size_t v_sz_2351_; size_t v___x_2352_; lean_object* v___x_2353_; 
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = lean_array_get_size(v_coinductiveElabData_2340_);
v___x_2350_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2340_, v___x_2348_, v___x_2349_);
v_sz_2351_ = lean_array_size(v_infos_2339_);
v___x_2352_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2339_);
v___x_2353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2339_, v_numParams_2338_, v_infos_2339_, v_sz_2351_, v___x_2352_, v___x_2350_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
lean_dec_ref(v_infos_2339_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2361_; 
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2361_ == 0)
{
lean_object* v_unused_2362_; 
v_unused_2362_ = lean_ctor_get(v___x_2353_, 0);
lean_dec(v_unused_2362_);
v___x_2355_ = v___x_2353_;
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
else
{
lean_dec(v___x_2353_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_box(0);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2357_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2353_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2353_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2371_, lean_object* v_infos_2372_, lean_object* v_coinductiveElabData_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2371_, v_infos_2372_, v_coinductiveElabData_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2382_, lean_object* v_infos_2383_, lean_object* v_numParams_2384_, lean_object* v_as_2385_, lean_object* v_as_x27_2386_, lean_object* v_b_2387_, lean_object* v_a_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2382_, v_infos_2383_, v_numParams_2384_, v_as_x27_2386_, v_b_2387_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2397_, lean_object* v_infos_2398_, lean_object* v_numParams_2399_, lean_object* v_as_2400_, lean_object* v_as_x27_2401_, lean_object* v_b_2402_, lean_object* v_a_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2397_, v_infos_2398_, v_numParams_2399_, v_as_2400_, v_as_x27_2401_, v_b_2402_, v_a_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v_as_x27_2401_);
lean_dec(v_as_2400_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2412_, lean_object* v_msg_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2422_, lean_object* v_msg_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2422_, v_msg_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2432_, lean_object* v_macroStack_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2432_, v_macroStack_2433_, v___y_2438_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2442_, lean_object* v_macroStack_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2442_, v_macroStack_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_mvarId_2452_, lean_object* v_x_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; 
v___x_2459_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2452_, v_x_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2459_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2459_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_mvarId_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2476_, v_x_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2484_, lean_object* v_mvarId_2485_, lean_object* v_x_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2485_, v_x_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2493_, lean_object* v_mvarId_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2493_, v_mvarId_2494_, v_x_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_type_2502_, lean_object* v_maxFVars_x3f_2503_, lean_object* v_k_2504_, uint8_t v_cleanupAnnotations_2505_, uint8_t v_whnfType_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___f_2512_; lean_object* v___x_2513_; 
v___f_2512_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2512_, 0, v_k_2504_);
v___x_2513_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2502_, v_maxFVars_x3f_2503_, v___f_2512_, v_cleanupAnnotations_2505_, v_whnfType_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2513_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2513_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
v_a_2522_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2513_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2513_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_type_2530_, lean_object* v_maxFVars_x3f_2531_, lean_object* v_k_2532_, lean_object* v_cleanupAnnotations_2533_, lean_object* v_whnfType_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2540_; uint8_t v_whnfType_boxed_2541_; lean_object* v_res_2542_; 
v_cleanupAnnotations_boxed_2540_ = lean_unbox(v_cleanupAnnotations_2533_);
v_whnfType_boxed_2541_ = lean_unbox(v_whnfType_2534_);
v_res_2542_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2530_, v_maxFVars_x3f_2531_, v_k_2532_, v_cleanupAnnotations_boxed_2540_, v_whnfType_boxed_2541_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2543_, lean_object* v_type_2544_, lean_object* v_maxFVars_x3f_2545_, lean_object* v_k_2546_, uint8_t v_cleanupAnnotations_2547_, uint8_t v_whnfType_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2544_, v_maxFVars_x3f_2545_, v_k_2546_, v_cleanupAnnotations_2547_, v_whnfType_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2555_, lean_object* v_type_2556_, lean_object* v_maxFVars_x3f_2557_, lean_object* v_k_2558_, lean_object* v_cleanupAnnotations_2559_, lean_object* v_whnfType_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2566_; uint8_t v_whnfType_boxed_2567_; lean_object* v_res_2568_; 
v_cleanupAnnotations_boxed_2566_ = lean_unbox(v_cleanupAnnotations_2559_);
v_whnfType_boxed_2567_ = lean_unbox(v_whnfType_2560_);
v_res_2568_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2555_, v_type_2556_, v_maxFVars_x3f_2557_, v_k_2558_, v_cleanupAnnotations_boxed_2566_, v_whnfType_boxed_2567_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2569_, lean_object* v_msg_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_toCold_2576_; lean_object* v_currRecDepth_2577_; lean_object* v_ref_2578_; uint16_t v_optionFlags_2579_; uint8_t v_suppressElabErrors_2580_; uint8_t v_isRecordingDeps_2581_; lean_object* v_ref_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v_toCold_2576_ = lean_ctor_get(v___y_2573_, 0);
v_currRecDepth_2577_ = lean_ctor_get(v___y_2573_, 1);
v_ref_2578_ = lean_ctor_get(v___y_2573_, 2);
v_optionFlags_2579_ = lean_ctor_get_uint16(v___y_2573_, sizeof(void*)*3);
v_suppressElabErrors_2580_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2581_ = lean_ctor_get_uint8(v___y_2573_, sizeof(void*)*3 + 3);
v_ref_2582_ = l_Lean_replaceRef(v_ref_2569_, v_ref_2578_);
lean_inc(v_currRecDepth_2577_);
lean_inc_ref(v_toCold_2576_);
v___x_2583_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2583_, 0, v_toCold_2576_);
lean_ctor_set(v___x_2583_, 1, v_currRecDepth_2577_);
lean_ctor_set(v___x_2583_, 2, v_ref_2582_);
lean_ctor_set_uint16(v___x_2583_, sizeof(void*)*3, v_optionFlags_2579_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*3 + 2, v_suppressElabErrors_2580_);
lean_ctor_set_uint8(v___x_2583_, sizeof(void*)*3 + 3, v_isRecordingDeps_2581_);
v___x_2584_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2570_, v___y_2571_, v___y_2572_, v___x_2583_, v___y_2574_);
lean_dec_ref_known(v___x_2583_, 3);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2585_, lean_object* v_msg_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2585_, v_msg_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v_ref_2585_);
return v_res_2592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2593_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2596_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2597_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2598_ = lean_unsigned_to_nat(0u);
v___x_2599_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
lean_ctor_set(v___x_2599_, 2, v___x_2598_);
lean_ctor_set(v___x_2599_, 3, v___x_2598_);
lean_ctor_set(v___x_2599_, 4, v___x_2597_);
lean_ctor_set(v___x_2599_, 5, v___x_2597_);
lean_ctor_set(v___x_2599_, 6, v___x_2597_);
lean_ctor_set(v___x_2599_, 7, v___x_2597_);
lean_ctor_set(v___x_2599_, 8, v___x_2597_);
lean_ctor_set(v___x_2599_, 9, v___x_2597_);
lean_ctor_set(v___x_2599_, 10, v___x_2596_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = lean_unsigned_to_nat(32u);
v___x_2601_ = lean_mk_empty_array_with_capacity(v___x_2600_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2603_ = ((size_t)5ULL);
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = lean_unsigned_to_nat(32u);
v___x_2606_ = lean_mk_empty_array_with_capacity(v___x_2605_);
v___x_2607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2608_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2606_);
lean_ctor_set(v___x_2608_, 2, v___x_2604_);
lean_ctor_set(v___x_2608_, 3, v___x_2604_);
lean_ctor_set_usize(v___x_2608_, 4, v___x_2603_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2609_ = lean_box(1);
v___x_2610_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2611_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2610_);
lean_ctor_set(v___x_2612_, 2, v___x_2609_);
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2615_ = l_Lean_stringToMessageData(v___x_2614_);
return v___x_2615_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2618_ = l_Lean_stringToMessageData(v___x_2617_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2620_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2621_ = l_Lean_stringToMessageData(v___x_2620_);
return v___x_2621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2624_ = l_Lean_stringToMessageData(v___x_2623_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2627_ = l_Lean_stringToMessageData(v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2630_ = l_Lean_stringToMessageData(v___x_2629_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2633_ = l_Lean_stringToMessageData(v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2634_, lean_object* v_declHint_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v_env_2640_; uint8_t v___x_2641_; 
v___x_2638_ = lean_box(0);
v___x_2639_ = lean_st_ref_get(v___y_2636_);
v_env_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc_ref(v_env_2640_);
lean_dec(v___x_2639_);
v___x_2641_ = l_Lean_Name_isAnonymous(v_declHint_2635_);
if (v___x_2641_ == 0)
{
uint8_t v_isExporting_2642_; 
v_isExporting_2642_ = lean_ctor_get_uint8(v_env_2640_, sizeof(void*)*13);
if (v_isExporting_2642_ == 0)
{
lean_object* v___x_2643_; 
lean_dec_ref(v_env_2640_);
lean_dec(v_declHint_2635_);
v___x_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2643_, 0, v_msg_2634_);
return v___x_2643_;
}
else
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
lean_inc_ref(v_env_2640_);
v___x_2644_ = l_Lean_Environment_setExporting(v_env_2640_, v___x_2641_);
lean_inc(v_declHint_2635_);
lean_inc_ref(v___x_2644_);
v___x_2645_ = l_Lean_Environment_contains(v___x_2644_, v_declHint_2635_, v_isExporting_2642_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; 
lean_dec_ref(v___x_2644_);
lean_dec_ref(v_env_2640_);
lean_dec(v_declHint_2635_);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v_msg_2634_);
return v___x_2646_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v_c_2652_; lean_object* v___x_2653_; 
v___x_2647_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2649_ = l_Lean_Options_empty;
v___x_2650_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2644_);
lean_ctor_set(v___x_2650_, 1, v___x_2647_);
lean_ctor_set(v___x_2650_, 2, v___x_2648_);
lean_ctor_set(v___x_2650_, 3, v___x_2649_);
lean_inc(v_declHint_2635_);
v___x_2651_ = l_Lean_MessageData_ofConstName(v_declHint_2635_, v___x_2641_);
v_c_2652_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2652_, 0, v___x_2650_);
lean_ctor_set(v_c_2652_, 1, v___x_2651_);
v___x_2653_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2640_, v_declHint_2635_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref(v_env_2640_);
lean_dec(v_declHint_2635_);
v___x_2654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2654_);
lean_ctor_set(v___x_2655_, 1, v_c_2652_);
v___x_2656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2655_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = l_Lean_MessageData_note(v___x_2657_);
v___x_2659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2659_, 0, v_msg_2634_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
else
{
lean_object* v_val_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2695_; 
v_val_2661_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2663_ = v___x_2653_;
v_isShared_2664_ = v_isSharedCheck_2695_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_val_2661_);
lean_dec(v___x_2653_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2695_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v_moduleNames_2666_; lean_object* v_mod_2667_; uint8_t v___x_2668_; 
v___x_2665_ = l_Lean_Environment_header(v_env_2640_);
lean_dec_ref(v_env_2640_);
v_moduleNames_2666_ = lean_ctor_get(v___x_2665_, 4);
lean_inc_ref(v_moduleNames_2666_);
lean_dec_ref(v___x_2665_);
v_mod_2667_ = lean_array_get(v___x_2638_, v_moduleNames_2666_, v_val_2661_);
lean_dec(v_val_2661_);
lean_dec_ref(v_moduleNames_2666_);
v___x_2668_ = l_Lean_isPrivateName(v_declHint_2635_);
lean_dec(v_declHint_2635_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v___x_2669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v_c_2652_);
v___x_2671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2670_);
lean_ctor_set(v___x_2672_, 1, v___x_2671_);
v___x_2673_ = l_Lean_MessageData_ofName(v_mod_2667_);
v___x_2674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2674_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = l_Lean_MessageData_note(v___x_2676_);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v_msg_2634_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2678_);
v___x_2680_ = v___x_2663_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v___x_2682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2682_);
lean_ctor_set(v___x_2683_, 1, v_c_2652_);
v___x_2684_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = l_Lean_MessageData_ofName(v_mod_2667_);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2687_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = l_Lean_MessageData_note(v___x_2689_);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_msg_2634_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set_tag(v___x_2663_, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2691_);
v___x_2693_ = v___x_2663_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2696_; 
lean_dec_ref(v_env_2640_);
lean_dec(v_declHint_2635_);
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_msg_2634_);
return v___x_2696_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2697_, lean_object* v_declHint_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2697_, v_declHint_2698_, v___y_2699_);
lean_dec(v___y_2699_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2702_, lean_object* v_declHint_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2719_; 
v___x_2709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2702_, v_declHint_2703_, v___y_2707_);
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2719_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2719_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2714_ = l_Lean_unknownIdentifierMessageTag;
v___x_2715_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v_a_2710_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 0, v___x_2715_);
v___x_2717_ = v___x_2712_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2720_, lean_object* v_declHint_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2720_, v_declHint_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2728_, lean_object* v_msg_2729_, lean_object* v_declHint_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v___x_2736_; lean_object* v_a_2737_; lean_object* v___x_2738_; 
v___x_2736_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2729_, v_declHint_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref(v___x_2736_);
v___x_2738_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2728_, v_a_2737_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2739_, lean_object* v_msg_2740_, lean_object* v_declHint_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2739_, v_msg_2740_, v_declHint_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v_ref_2739_);
return v_res_2747_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2751_, lean_object* v_constName_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2758_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2759_ = 0;
lean_inc(v_constName_2752_);
v___x_2760_ = l_Lean_MessageData_ofConstName(v_constName_2752_, v___x_2759_);
v___x_2761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2758_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2751_, v___x_2763_, v_constName_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2765_, lean_object* v_constName_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2765_, v_constName_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v_ref_2765_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v_ref_2779_; lean_object* v___x_2780_; 
v_ref_2779_ = lean_ctor_get(v___y_2776_, 2);
v___x_2780_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2779_, v_constName_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; lean_object* v_env_2795_; uint8_t v___x_2796_; lean_object* v___x_2797_; 
v___x_2794_ = lean_st_ref_get(v___y_2792_);
v_env_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc_ref(v_env_2795_);
lean_dec(v___x_2794_);
v___x_2796_ = 0;
lean_inc(v_constName_2788_);
v___x_2797_ = l_Lean_Environment_find_x3f(v_env_2795_, v_constName_2788_, v___x_2796_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2798_;
}
else
{
lean_object* v_val_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v_constName_2788_);
v_val_2799_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2797_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_val_2799_);
lean_dec(v___x_2797_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
lean_ctor_set_tag(v___x_2801_, 0);
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_val_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v_res_2813_; 
v_res_2813_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
return v_res_2813_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2814_, lean_object* v_as_2815_, size_t v_i_2816_, size_t v_stop_2817_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_usize_dec_eq(v_i_2816_, v_stop_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; uint8_t v___x_2820_; 
v___x_2819_ = lean_array_uget_borrowed(v_as_2815_, v_i_2816_);
v___x_2820_ = l_Lean_Expr_isAppOf(v_e_2814_, v___x_2819_);
if (v___x_2820_ == 0)
{
size_t v___x_2821_; size_t v___x_2822_; 
v___x_2821_ = ((size_t)1ULL);
v___x_2822_ = lean_usize_add(v_i_2816_, v___x_2821_);
v_i_2816_ = v___x_2822_;
goto _start;
}
else
{
return v___x_2820_;
}
}
else
{
uint8_t v___x_2824_; 
v___x_2824_ = 0;
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2825_, lean_object* v_as_2826_, lean_object* v_i_2827_, lean_object* v_stop_2828_){
_start:
{
size_t v_i_boxed_2829_; size_t v_stop_boxed_2830_; uint8_t v_res_2831_; lean_object* v_r_2832_; 
v_i_boxed_2829_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_stop_boxed_2830_ = lean_unbox_usize(v_stop_2828_);
lean_dec(v_stop_2828_);
v_res_2831_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2825_, v_as_2826_, v_i_boxed_2829_, v_stop_boxed_2830_);
lean_dec_ref(v_as_2826_);
lean_dec_ref(v_e_2825_);
v_r_2832_ = lean_box(v_res_2831_);
return v_r_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2833_, lean_object* v_name_2834_, lean_object* v___y_2835_, lean_object* v___x_2836_, lean_object* v_levels_2837_, lean_object* v_params_2838_, lean_object* v_e_2839_){
_start:
{
uint8_t v___x_2840_; 
v___x_2840_ = l_Lean_Expr_isApp(v_e_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref(v_e_2839_);
lean_dec_ref(v_params_2838_);
lean_dec(v_levels_2837_);
lean_dec(v_name_2834_);
lean_dec(v_numParams_2833_);
v___x_2841_ = lean_box(0);
return v___x_2841_;
}
else
{
lean_object* v_dummy_2842_; lean_object* v_nargs_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_dummy_2842_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2843_ = l_Lean_Expr_getAppNumArgs(v_e_2839_);
lean_inc(v_nargs_2843_);
v___x_2844_ = lean_mk_array(v_nargs_2843_, v_dummy_2842_);
v___x_2845_ = lean_unsigned_to_nat(1u);
v___x_2846_ = lean_nat_sub(v_nargs_2843_, v___x_2845_);
lean_dec(v_nargs_2843_);
lean_inc_ref(v_e_2839_);
v___x_2847_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2839_, v___x_2844_, v___x_2846_);
v___x_2848_ = lean_array_get_size(v___x_2847_);
v___x_2849_ = l_Array_toSubarray___redArg(v___x_2847_, v_numParams_2833_, v___x_2848_);
v___x_2850_ = l_Lean_Expr_isAppOf(v_e_2839_, v_name_2834_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; uint8_t v___x_2852_; 
lean_dec(v_name_2834_);
v___x_2851_ = lean_array_get_size(v___y_2835_);
v___x_2852_ = lean_nat_dec_lt(v___x_2836_, v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref(v___x_2849_);
lean_dec_ref(v_e_2839_);
lean_dec_ref(v_params_2838_);
lean_dec(v_levels_2837_);
v___x_2853_ = lean_box(0);
return v___x_2853_;
}
else
{
if (v___x_2852_ == 0)
{
lean_object* v___x_2854_; 
lean_dec_ref(v___x_2849_);
lean_dec_ref(v_e_2839_);
lean_dec_ref(v_params_2838_);
lean_dec(v_levels_2837_);
v___x_2854_ = lean_box(0);
return v___x_2854_;
}
else
{
size_t v___x_2855_; size_t v___x_2856_; uint8_t v___x_2857_; 
v___x_2855_ = ((size_t)0ULL);
v___x_2856_ = lean_usize_of_nat(v___x_2851_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2839_, v___y_2835_, v___x_2855_, v___x_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; 
lean_dec_ref(v___x_2849_);
lean_dec_ref(v_e_2839_);
lean_dec_ref(v_params_2838_);
lean_dec(v_levels_2837_);
v___x_2858_ = lean_box(0);
return v___x_2858_;
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2859_ = l_Lean_Expr_getAppFn(v_e_2839_);
lean_dec_ref(v_e_2839_);
v___x_2860_ = l_Lean_Expr_constName(v___x_2859_);
lean_dec_ref(v___x_2859_);
v___x_2861_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2860_);
v___x_2862_ = l_Lean_mkConst(v___x_2861_, v_levels_2837_);
v___x_2863_ = l_Subarray_copy___redArg(v___x_2849_);
v___x_2864_ = l_Array_append___redArg(v_params_2838_, v___x_2863_);
lean_dec_ref(v___x_2863_);
v___x_2865_ = l_Lean_mkAppN(v___x_2862_, v___x_2864_);
lean_dec_ref(v___x_2864_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
return v___x_2866_;
}
}
}
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
lean_dec_ref(v_e_2839_);
v___x_2867_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2834_);
v___x_2868_ = l_Lean_mkConst(v___x_2867_, v_levels_2837_);
v___x_2869_ = l_Subarray_copy___redArg(v___x_2849_);
v___x_2870_ = l_Array_append___redArg(v_params_2838_, v___x_2869_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = l_Lean_mkAppN(v___x_2868_, v___x_2870_);
lean_dec_ref(v___x_2870_);
v___x_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2871_);
return v___x_2872_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2873_, lean_object* v_name_2874_, lean_object* v___y_2875_, lean_object* v___x_2876_, lean_object* v_levels_2877_, lean_object* v_params_2878_, lean_object* v_e_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2873_, v_name_2874_, v___y_2875_, v___x_2876_, v_levels_2877_, v_params_2878_, v_e_2879_);
lean_dec(v___x_2876_);
lean_dec_ref(v___y_2875_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v_eqProof_2881_, lean_object* v___x_2882_, lean_object* v_eNew_2883_, lean_object* v_snd_2884_, lean_object* v___x_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_Meta_mkEqMP(v_eqProof_2881_, v___x_2882_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_eNew_2883_);
v___x_2894_ = lean_box(0);
v___x_2895_ = l_Lean_MVarId_replace(v_snd_2884_, v___x_2885_, v_a_2892_, v___x_2893_, v___x_2894_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
return v___x_2895_;
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v___x_2885_);
lean_dec(v_snd_2884_);
lean_dec_ref(v_eNew_2883_);
v_a_2896_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2891_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2891_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object* v_eqProof_2904_, lean_object* v___x_2905_, lean_object* v_eNew_2906_, lean_object* v_snd_2907_, lean_object* v___x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_2904_, v___x_2905_, v_eNew_2906_, v_snd_2907_, v___x_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2914_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0));
v___x_2917_ = l_Lean_stringToMessageData(v___x_2916_);
return v___x_2917_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9));
v___x_2940_ = l_Lean_stringToMessageData(v___x_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_2941_, lean_object* v___x_2942_, lean_object* v___x_2943_, uint8_t v___x_2944_, lean_object* v___x_2945_, lean_object* v___x_2946_, uint8_t v___x_2947_, lean_object* v_params_2948_, lean_object* v_args_2949_, lean_object* v_indices_2950_, uint8_t v___x_2951_, lean_object* v_a_2952_, lean_object* v___x_2953_, lean_object* v___x_2954_, lean_object* v___f_2955_, lean_object* v___x_2956_, lean_object* v_targetArgs_2957_, lean_object* v_x_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = lean_array_get_size(v_targetArgs_2957_);
v___x_2965_ = lean_nat_dec_eq(v___x_2964_, v___x_2941_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
lean_dec_ref(v___x_2946_);
lean_dec(v___x_2945_);
lean_dec_ref(v___x_2943_);
v___x_2966_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_2967_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_2966_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2967_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_array_fget_borrowed(v_targetArgs_2957_, v___x_2942_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc_ref(v___x_2943_);
v___x_2969_ = lean_infer_type(v___x_2943_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
if (lean_obj_tag(v_a_2970_) == 7)
{
lean_object* v_binderType_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v_binderType_2971_ = lean_ctor_get(v_a_2970_, 1);
lean_inc_ref(v_binderType_2971_);
lean_dec_ref_known(v_a_2970_, 3);
v___x_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_binderType_2971_);
v___x_2973_ = l_Lean_Meta_mkFreshExprMVar(v___x_2972_, v___x_2944_, v___x_2945_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2975_ = l_Lean_Expr_mvarId_x21(v_a_2974_);
v___x_2976_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2975_, v___x_2946_, v___x_2947_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v___x_2978_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2976_, 1);
lean_inc(v___x_2968_);
v___x_2978_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2977_, v___x_2968_, v___y_2960_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3060_; 
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v___x_2978_, 0);
lean_dec(v_unused_3061_);
v___x_2980_ = v___x_2978_;
v_isShared_2981_ = v_isSharedCheck_3060_;
goto v_resetjp_2979_;
}
else
{
lean_dec(v___x_2978_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3060_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; lean_object* v___x_2987_; 
v___x_2982_ = l_Lean_Expr_app___override(v___x_2943_, v_a_2974_);
lean_inc_ref(v_params_2948_);
v___x_2983_ = l_Array_append___redArg(v_params_2948_, v_args_2949_);
v___x_2984_ = l_Array_append___redArg(v___x_2983_, v_indices_2950_);
v___x_2985_ = l_Array_append___redArg(v___x_2984_, v_targetArgs_2957_);
v___x_2986_ = 1;
v___x_2987_ = l_Lean_Meta_mkLambdaFVars(v___x_2985_, v___x_2982_, v___x_2951_, v___x_2947_, v___x_2951_, v___x_2947_, v___x_2986_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec_ref(v___x_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_2988_, v___y_2960_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = l_Lean_ConstantInfo_levelParams(v_a_2952_);
v___x_2992_ = l_Lean_mkCasesOnName(v___x_2953_);
v___x_2993_ = l_Lean_Meta_mkForallFVars(v_params_2948_, v___x_2954_, v___x_2951_, v___x_2947_, v___x_2947_, v___x_2986_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec_ref(v_params_2948_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
v___x_2995_ = lean_box(0);
lean_inc(v___x_2992_);
v___x_2996_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_2992_, v___x_2991_, v_a_2994_, v_a_2990_, v___x_2995_, v___y_2962_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; lean_object* v___x_2999_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref_known(v___x_2996_, 1);
if (v_isShared_2981_ == 0)
{
lean_ctor_set_tag(v___x_2980_, 1);
lean_ctor_set(v___x_2980_, 0, v_a_2997_);
v___x_2999_ = v___x_2980_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_2997_);
v___x_2999_ = v_reuseFailAlloc_3027_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_addDecl(v___x_2999_, v___x_2951_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec_ref_known(v___x_3000_, 1);
v___x_3001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8));
v___x_3002_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3002_, 0, v___x_2992_);
lean_closure_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = lean_box(0);
v___x_3004_ = lean_box(0);
v___x_3005_ = lean_box(1);
v___x_3006_ = lean_mk_empty_array_with_capacity(v___x_2942_);
v___x_3007_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3007_, 0, v___x_3003_);
lean_ctor_set(v___x_3007_, 1, v___x_3004_);
lean_ctor_set(v___x_3007_, 2, v___x_3003_);
lean_ctor_set(v___x_3007_, 3, v___f_2955_);
lean_ctor_set(v___x_3007_, 4, v___x_3005_);
lean_ctor_set(v___x_3007_, 5, v___x_3005_);
lean_ctor_set(v___x_3007_, 6, v___x_3003_);
lean_ctor_set(v___x_3007_, 7, v___x_3006_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8, v___x_2947_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 1, v___x_2947_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 2, v___x_2947_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 3, v___x_2947_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 4, v___x_2951_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 5, v___x_2951_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 6, v___x_2951_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 7, v___x_2951_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 8, v___x_2947_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 9, v___x_2951_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*8 + 10, v___x_2947_);
v___x_3008_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3008_, 0, v___x_2956_);
lean_ctor_set(v___x_3008_, 1, v___x_3005_);
lean_ctor_set(v___x_3008_, 2, v___x_3004_);
lean_ctor_set(v___x_3008_, 3, v___x_3004_);
lean_ctor_set(v___x_3008_, 4, v___x_3004_);
lean_ctor_set(v___x_3008_, 5, v___x_3005_);
lean_ctor_set(v___x_3008_, 6, v___x_3004_);
v___x_3009_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3002_, v___x_3007_, v___x_3008_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3018_; 
v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3012_ = v___x_3009_;
v_isShared_3013_ = v_isSharedCheck_3018_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v___x_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3018_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v_fst_3014_; lean_object* v___x_3016_; 
v_fst_3014_ = lean_ctor_get(v_a_3010_, 0);
lean_inc(v_fst_3014_);
lean_dec(v_a_3010_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v_fst_3014_);
v___x_3016_ = v___x_3012_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_fst_3014_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v_a_3019_ = lean_ctor_get(v___x_3009_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_3009_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_3009_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_dec(v___x_2992_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
return v___x_3000_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v___x_2992_);
lean_del_object(v___x_2980_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
v_a_3028_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2996_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2996_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v___x_2992_);
lean_dec(v___x_2991_);
lean_dec(v_a_2990_);
lean_del_object(v___x_2980_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
v_a_3036_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_2993_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_2993_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_del_object(v___x_2980_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
v_a_3044_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2989_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2989_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_del_object(v___x_2980_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
v_a_3052_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_2987_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_2987_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
}
else
{
lean_dec(v_a_2974_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
lean_dec_ref(v___x_2943_);
return v___x_2978_;
}
}
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v_a_2974_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
lean_dec_ref(v___x_2943_);
v_a_3062_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2976_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_2976_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
lean_dec_ref(v___x_2946_);
lean_dec_ref(v___x_2943_);
v_a_3070_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2973_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2973_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_dec(v_a_2970_);
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
lean_dec_ref(v___x_2946_);
lean_dec(v___x_2945_);
lean_dec_ref(v___x_2943_);
v___x_3078_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3079_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3078_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_3079_;
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v___x_2956_);
lean_dec_ref(v___f_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v___x_2953_);
lean_dec_ref(v_params_2948_);
lean_dec_ref(v___x_2946_);
lean_dec(v___x_2945_);
lean_dec_ref(v___x_2943_);
v_a_3080_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_2969_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_2969_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3088_ = _args[0];
lean_object* v___x_3089_ = _args[1];
lean_object* v___x_3090_ = _args[2];
lean_object* v___x_3091_ = _args[3];
lean_object* v___x_3092_ = _args[4];
lean_object* v___x_3093_ = _args[5];
lean_object* v___x_3094_ = _args[6];
lean_object* v_params_3095_ = _args[7];
lean_object* v_args_3096_ = _args[8];
lean_object* v_indices_3097_ = _args[9];
lean_object* v___x_3098_ = _args[10];
lean_object* v_a_3099_ = _args[11];
lean_object* v___x_3100_ = _args[12];
lean_object* v___x_3101_ = _args[13];
lean_object* v___f_3102_ = _args[14];
lean_object* v___x_3103_ = _args[15];
lean_object* v_targetArgs_3104_ = _args[16];
lean_object* v_x_3105_ = _args[17];
lean_object* v___y_3106_ = _args[18];
lean_object* v___y_3107_ = _args[19];
lean_object* v___y_3108_ = _args[20];
lean_object* v___y_3109_ = _args[21];
lean_object* v___y_3110_ = _args[22];
_start:
{
uint8_t v___x_16299__boxed_3111_; uint8_t v___x_16302__boxed_3112_; uint8_t v___x_16303__boxed_3113_; lean_object* v_res_3114_; 
v___x_16299__boxed_3111_ = lean_unbox(v___x_3091_);
v___x_16302__boxed_3112_ = lean_unbox(v___x_3094_);
v___x_16303__boxed_3113_ = lean_unbox(v___x_3098_);
v_res_3114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3088_, v___x_3089_, v___x_3090_, v___x_16299__boxed_3111_, v___x_3092_, v___x_3093_, v___x_16302__boxed_3112_, v_params_3095_, v_args_3096_, v_indices_3097_, v___x_16303__boxed_3113_, v_a_3099_, v___x_3100_, v___x_3101_, v___f_3102_, v___x_3103_, v_targetArgs_3104_, v_x_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec_ref(v_x_3105_);
lean_dec_ref(v_targetArgs_3104_);
lean_dec_ref(v_a_3099_);
lean_dec_ref(v_indices_3097_);
lean_dec_ref(v_args_3096_);
lean_dec(v___x_3089_);
lean_dec(v___x_3088_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3115_, lean_object* v___x_3116_, lean_object* v___x_3117_, uint8_t v___x_3118_, lean_object* v___x_3119_, lean_object* v___x_3120_, uint8_t v___x_3121_, lean_object* v_params_3122_, lean_object* v_args_3123_, uint8_t v___x_3124_, lean_object* v_a_3125_, lean_object* v___x_3126_, lean_object* v___x_3127_, lean_object* v___f_3128_, lean_object* v___x_3129_, lean_object* v___x_3130_, lean_object* v_indices_3131_, lean_object* v_goalType_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___f_3142_; lean_object* v___x_3143_; 
v___x_3138_ = l_Lean_mkAppN(v___x_3115_, v_indices_3131_);
v___x_3139_ = lean_box(v___x_3118_);
v___x_3140_ = lean_box(v___x_3121_);
v___x_3141_ = lean_box(v___x_3124_);
v___f_3142_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 23, 16);
lean_closure_set(v___f_3142_, 0, v___x_3116_);
lean_closure_set(v___f_3142_, 1, v___x_3117_);
lean_closure_set(v___f_3142_, 2, v___x_3138_);
lean_closure_set(v___f_3142_, 3, v___x_3139_);
lean_closure_set(v___f_3142_, 4, v___x_3119_);
lean_closure_set(v___f_3142_, 5, v___x_3120_);
lean_closure_set(v___f_3142_, 6, v___x_3140_);
lean_closure_set(v___f_3142_, 7, v_params_3122_);
lean_closure_set(v___f_3142_, 8, v_args_3123_);
lean_closure_set(v___f_3142_, 9, v_indices_3131_);
lean_closure_set(v___f_3142_, 10, v___x_3141_);
lean_closure_set(v___f_3142_, 11, v_a_3125_);
lean_closure_set(v___f_3142_, 12, v___x_3126_);
lean_closure_set(v___f_3142_, 13, v___x_3127_);
lean_closure_set(v___f_3142_, 14, v___f_3128_);
lean_closure_set(v___f_3142_, 15, v___x_3129_);
v___x_3143_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3132_, v___x_3130_, v___f_3142_, v___x_3124_, v___x_3124_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3144_ = _args[0];
lean_object* v___x_3145_ = _args[1];
lean_object* v___x_3146_ = _args[2];
lean_object* v___x_3147_ = _args[3];
lean_object* v___x_3148_ = _args[4];
lean_object* v___x_3149_ = _args[5];
lean_object* v___x_3150_ = _args[6];
lean_object* v_params_3151_ = _args[7];
lean_object* v_args_3152_ = _args[8];
lean_object* v___x_3153_ = _args[9];
lean_object* v_a_3154_ = _args[10];
lean_object* v___x_3155_ = _args[11];
lean_object* v___x_3156_ = _args[12];
lean_object* v___f_3157_ = _args[13];
lean_object* v___x_3158_ = _args[14];
lean_object* v___x_3159_ = _args[15];
lean_object* v_indices_3160_ = _args[16];
lean_object* v_goalType_3161_ = _args[17];
lean_object* v___y_3162_ = _args[18];
lean_object* v___y_3163_ = _args[19];
lean_object* v___y_3164_ = _args[20];
lean_object* v___y_3165_ = _args[21];
lean_object* v___y_3166_ = _args[22];
_start:
{
uint8_t v___x_16635__boxed_3167_; uint8_t v___x_16638__boxed_3168_; uint8_t v___x_16639__boxed_3169_; lean_object* v_res_3170_; 
v___x_16635__boxed_3167_ = lean_unbox(v___x_3147_);
v___x_16638__boxed_3168_ = lean_unbox(v___x_3150_);
v___x_16639__boxed_3169_ = lean_unbox(v___x_3153_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3144_, v___x_3145_, v___x_3146_, v___x_16635__boxed_3167_, v___x_3148_, v___x_3149_, v___x_16638__boxed_3168_, v_params_3151_, v_args_3152_, v___x_16639__boxed_3169_, v_a_3154_, v___x_3155_, v___x_3156_, v___f_3157_, v___x_3158_, v___x_3159_, v_indices_3160_, v_goalType_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object* v___x_3171_, uint8_t v___x_3172_, lean_object* v_snd_3173_, lean_object* v___x_3174_, uint8_t v___x_3175_, lean_object* v___x_3176_, lean_object* v___x_3177_, lean_object* v_a_3178_, lean_object* v___x_3179_, lean_object* v___x_3180_, uint8_t v___x_3181_, lean_object* v___x_3182_, lean_object* v_params_3183_, lean_object* v_args_3184_, lean_object* v_a_3185_, lean_object* v___x_3186_, lean_object* v___x_3187_, lean_object* v___f_3188_, lean_object* v___x_3189_, lean_object* v___x_3190_, lean_object* v_numIndices_3191_, lean_object* v_goalType_3192_, lean_object* v___x_3193_, lean_object* v___x_3194_, lean_object* v_fst_3195_, lean_object* v___x_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
lean_object* v_lctx_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; uint8_t v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_lctx_3202_ = lean_ctor_get(v___y_3197_, 2);
lean_inc(v___x_3171_);
lean_inc_ref(v_lctx_3202_);
v___x_3203_ = l_Lean_LocalContext_get_x21(v_lctx_3202_, v___x_3171_);
v___x_3204_ = l_Lean_LocalDecl_type(v___x_3203_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = 2;
v___x_3206_ = lean_box(0);
v___x_3207_ = 0;
v___x_3208_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3208_, 0, v___x_3206_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*1, v___x_3205_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*1 + 1, v___x_3172_);
lean_ctor_set_uint8(v___x_3208_, sizeof(void*)*1 + 2, v___x_3207_);
lean_inc_ref(v___x_3174_);
lean_inc(v_snd_3173_);
v___x_3209_ = l_Lean_MVarId_rewrite(v_snd_3173_, v___x_3204_, v___x_3174_, v___x_3172_, v___x_3208_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v_eNew_3211_; lean_object* v_eqProof_3212_; lean_object* v___x_3213_; lean_object* v___f_3214_; lean_object* v___x_3215_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v_eNew_3211_ = lean_ctor_get(v_a_3210_, 0);
lean_inc_ref(v_eNew_3211_);
v_eqProof_3212_ = lean_ctor_get(v_a_3210_, 1);
lean_inc_ref(v_eqProof_3212_);
lean_dec(v_a_3210_);
lean_inc(v___x_3171_);
v___x_3213_ = l_Lean_mkFVar(v___x_3171_);
lean_inc(v_snd_3173_);
v___f_3214_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3214_, 0, v_eqProof_3212_);
lean_closure_set(v___f_3214_, 1, v___x_3213_);
lean_closure_set(v___f_3214_, 2, v_eNew_3211_);
lean_closure_set(v___f_3214_, 3, v_snd_3173_);
lean_closure_set(v___f_3214_, 4, v___x_3171_);
v___x_3215_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3173_, v___f_3214_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___y_3218_; uint8_t v___x_3246_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___x_3246_ = lean_nat_dec_lt(v___x_3193_, v___x_3194_);
if (v___x_3246_ == 0)
{
v___y_3218_ = v_fst_3195_;
goto v___jp_3217_;
}
else
{
lean_object* v_fvarId_3247_; lean_object* v_xs_x27_3248_; lean_object* v___x_3249_; 
v_fvarId_3247_ = lean_ctor_get(v_a_3216_, 0);
v_xs_x27_3248_ = lean_array_fset(v_fst_3195_, v___x_3193_, v___x_3196_);
lean_inc(v_fvarId_3247_);
v___x_3249_ = lean_array_fset(v_xs_x27_3248_, v___x_3193_, v_fvarId_3247_);
v___y_3218_ = v___x_3249_;
goto v___jp_3217_;
}
v___jp_3217_:
{
lean_object* v_mvarId_3219_; lean_object* v___x_3220_; 
v_mvarId_3219_ = lean_ctor_get(v_a_3216_, 1);
lean_inc(v_mvarId_3219_);
lean_dec(v_a_3216_);
v___x_3220_ = l_Lean_MVarId_revert(v_mvarId_3219_, v___y_3218_, v___x_3175_, v___x_3175_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v_snd_3222_; lean_object* v___x_3223_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v_snd_3222_ = lean_ctor_get(v_a_3221_, 1);
lean_inc(v_snd_3222_);
lean_dec(v_a_3221_);
v___x_3223_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3222_, v___x_3176_, v___y_3198_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3236_; 
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v___x_3223_, 0);
lean_dec(v_unused_3237_);
v___x_3225_ = v___x_3223_;
v_isShared_3226_ = v_isSharedCheck_3236_;
goto v_resetjp_3224_;
}
else
{
lean_dec(v___x_3223_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3236_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___f_3231_; lean_object* v___x_3233_; 
v___x_3227_ = l_Lean_Expr_app___override(v___x_3177_, v_a_3178_);
v___x_3228_ = lean_box(v___x_3181_);
v___x_3229_ = lean_box(v___x_3172_);
v___x_3230_ = lean_box(v___x_3175_);
v___f_3231_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 23, 16);
lean_closure_set(v___f_3231_, 0, v___x_3227_);
lean_closure_set(v___f_3231_, 1, v___x_3179_);
lean_closure_set(v___f_3231_, 2, v___x_3180_);
lean_closure_set(v___f_3231_, 3, v___x_3228_);
lean_closure_set(v___f_3231_, 4, v___x_3182_);
lean_closure_set(v___f_3231_, 5, v___x_3174_);
lean_closure_set(v___f_3231_, 6, v___x_3229_);
lean_closure_set(v___f_3231_, 7, v_params_3183_);
lean_closure_set(v___f_3231_, 8, v_args_3184_);
lean_closure_set(v___f_3231_, 9, v___x_3230_);
lean_closure_set(v___f_3231_, 10, v_a_3185_);
lean_closure_set(v___f_3231_, 11, v___x_3186_);
lean_closure_set(v___f_3231_, 12, v___x_3187_);
lean_closure_set(v___f_3231_, 13, v___f_3188_);
lean_closure_set(v___f_3231_, 14, v___x_3189_);
lean_closure_set(v___f_3231_, 15, v___x_3190_);
if (v_isShared_3226_ == 0)
{
lean_ctor_set_tag(v___x_3225_, 1);
lean_ctor_set(v___x_3225_, 0, v_numIndices_3191_);
v___x_3233_ = v___x_3225_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_numIndices_3191_);
v___x_3233_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3192_, v___x_3233_, v___f_3231_, v___x_3175_, v___x_3175_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec_ref(v___y_3197_);
return v___x_3234_;
}
}
}
else
{
lean_dec_ref(v___y_3197_);
lean_dec_ref(v_goalType_3192_);
lean_dec(v_numIndices_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec_ref(v___f_3188_);
lean_dec_ref(v___x_3187_);
lean_dec(v___x_3186_);
lean_dec_ref(v_a_3185_);
lean_dec_ref(v_args_3184_);
lean_dec_ref(v_params_3183_);
lean_dec(v___x_3182_);
lean_dec(v___x_3180_);
lean_dec(v___x_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3174_);
return v___x_3223_;
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec_ref(v___y_3197_);
lean_dec_ref(v_goalType_3192_);
lean_dec(v_numIndices_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec_ref(v___f_3188_);
lean_dec_ref(v___x_3187_);
lean_dec(v___x_3186_);
lean_dec_ref(v_a_3185_);
lean_dec_ref(v_args_3184_);
lean_dec_ref(v_params_3183_);
lean_dec(v___x_3182_);
lean_dec(v___x_3180_);
lean_dec(v___x_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3174_);
v_a_3238_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3220_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3220_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v___y_3197_);
lean_dec_ref(v_fst_3195_);
lean_dec_ref(v_goalType_3192_);
lean_dec(v_numIndices_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec_ref(v___f_3188_);
lean_dec_ref(v___x_3187_);
lean_dec(v___x_3186_);
lean_dec_ref(v_a_3185_);
lean_dec_ref(v_args_3184_);
lean_dec_ref(v_params_3183_);
lean_dec(v___x_3182_);
lean_dec(v___x_3180_);
lean_dec(v___x_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3174_);
v_a_3250_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3215_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3215_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v___y_3197_);
lean_dec_ref(v_fst_3195_);
lean_dec_ref(v_goalType_3192_);
lean_dec(v_numIndices_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec_ref(v___f_3188_);
lean_dec_ref(v___x_3187_);
lean_dec(v___x_3186_);
lean_dec_ref(v_a_3185_);
lean_dec_ref(v_args_3184_);
lean_dec_ref(v_params_3183_);
lean_dec(v___x_3182_);
lean_dec(v___x_3180_);
lean_dec(v___x_3179_);
lean_dec_ref(v_a_3178_);
lean_dec_ref(v___x_3177_);
lean_dec_ref(v___x_3176_);
lean_dec_ref(v___x_3174_);
lean_dec(v_snd_3173_);
lean_dec(v___x_3171_);
v_a_3258_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3209_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3209_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object** _args){
lean_object* v___x_3266_ = _args[0];
lean_object* v___x_3267_ = _args[1];
lean_object* v_snd_3268_ = _args[2];
lean_object* v___x_3269_ = _args[3];
lean_object* v___x_3270_ = _args[4];
lean_object* v___x_3271_ = _args[5];
lean_object* v___x_3272_ = _args[6];
lean_object* v_a_3273_ = _args[7];
lean_object* v___x_3274_ = _args[8];
lean_object* v___x_3275_ = _args[9];
lean_object* v___x_3276_ = _args[10];
lean_object* v___x_3277_ = _args[11];
lean_object* v_params_3278_ = _args[12];
lean_object* v_args_3279_ = _args[13];
lean_object* v_a_3280_ = _args[14];
lean_object* v___x_3281_ = _args[15];
lean_object* v___x_3282_ = _args[16];
lean_object* v___f_3283_ = _args[17];
lean_object* v___x_3284_ = _args[18];
lean_object* v___x_3285_ = _args[19];
lean_object* v_numIndices_3286_ = _args[20];
lean_object* v_goalType_3287_ = _args[21];
lean_object* v___x_3288_ = _args[22];
lean_object* v___x_3289_ = _args[23];
lean_object* v_fst_3290_ = _args[24];
lean_object* v___x_3291_ = _args[25];
lean_object* v___y_3292_ = _args[26];
lean_object* v___y_3293_ = _args[27];
lean_object* v___y_3294_ = _args[28];
lean_object* v___y_3295_ = _args[29];
lean_object* v___y_3296_ = _args[30];
_start:
{
uint8_t v___x_16702__boxed_3297_; uint8_t v___x_16705__boxed_3298_; uint8_t v___x_16711__boxed_3299_; lean_object* v_res_3300_; 
v___x_16702__boxed_3297_ = lean_unbox(v___x_3267_);
v___x_16705__boxed_3298_ = lean_unbox(v___x_3270_);
v___x_16711__boxed_3299_ = lean_unbox(v___x_3276_);
v_res_3300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3266_, v___x_16702__boxed_3297_, v_snd_3268_, v___x_3269_, v___x_16705__boxed_3298_, v___x_3271_, v___x_3272_, v_a_3273_, v___x_3274_, v___x_3275_, v___x_16711__boxed_3299_, v___x_3277_, v_params_3278_, v_args_3279_, v_a_3280_, v___x_3281_, v___x_3282_, v___f_3283_, v___x_3284_, v___x_3285_, v_numIndices_3286_, v_goalType_3287_, v___x_3288_, v___x_3289_, v_fst_3290_, v___x_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
return v_res_3300_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t v___x_3301_, lean_object* v_x_3302_){
_start:
{
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object* v___x_3303_, lean_object* v_x_3304_){
_start:
{
uint8_t v___x_16901__boxed_3305_; uint8_t v_res_3306_; lean_object* v_r_3307_; 
v___x_16901__boxed_3305_ = lean_unbox(v___x_3303_);
v_res_3306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_16901__boxed_3305_, v_x_3304_);
lean_dec(v_x_3304_);
v_r_3307_ = lean_box(v_res_3306_);
return v_r_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object* v___x_3311_, lean_object* v_a_3312_, lean_object* v___x_3313_, lean_object* v_numIndices_3314_, lean_object* v___x_3315_, lean_object* v___x_3316_, lean_object* v___x_3317_, lean_object* v_params_3318_, lean_object* v_a_3319_, lean_object* v___x_3320_, lean_object* v___x_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v_args_3324_, lean_object* v_goalType_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; uint8_t v___x_3332_; 
v___x_3331_ = lean_array_get_size(v_args_3324_);
v___x_3332_ = lean_nat_dec_eq(v___x_3331_, v___x_3311_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec_ref(v_goalType_3325_);
lean_dec_ref(v_args_3324_);
lean_dec(v___x_3322_);
lean_dec_ref(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_a_3319_);
lean_dec_ref(v_params_3318_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3316_);
lean_dec(v_numIndices_3314_);
lean_dec(v___x_3313_);
lean_dec(v___x_3311_);
v___x_3333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3334_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3333_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3334_;
}
else
{
if (lean_obj_tag(v_a_3312_) == 7)
{
lean_object* v_binderType_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v_binderType_3335_ = lean_ctor_get(v_a_3312_, 1);
v___x_3336_ = lean_array_fget(v_args_3324_, v___x_3313_);
lean_inc_ref(v_binderType_3335_);
v___x_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3337_, 0, v_binderType_3335_);
v___x_3338_ = 0;
v___x_3339_ = lean_box(0);
v___x_3340_ = l_Lean_Meta_mkFreshExprMVar(v___x_3337_, v___x_3338_, v___x_3339_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v_a_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; lean_object* v___f_3346_; lean_object* v___x_3347_; 
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref_known(v___x_3340_, 1);
v___x_3342_ = l_Lean_Expr_mvarId_x21(v_a_3341_);
v___x_3343_ = lean_nat_add(v_numIndices_3314_, v___x_3311_);
v___x_3344_ = lean_box(0);
v___x_3345_ = 0;
v___f_3346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0));
v___x_3347_ = l_Lean_Meta_introNCore(v___x_3342_, v___x_3343_, v___x_3344_, v___x_3345_, v___x_3345_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v_fst_3349_ = lean_ctor_get(v_a_3348_, 0);
lean_inc(v_fst_3349_);
v_snd_3350_ = lean_ctor_get(v_a_3348_, 1);
lean_inc_n(v_snd_3350_, 2);
lean_dec(v_a_3348_);
v___x_3351_ = lean_array_get_size(v_fst_3349_);
v___x_3352_ = lean_nat_sub(v___x_3351_, v___x_3311_);
v___x_3353_ = lean_array_get(v___x_3315_, v_fst_3349_, v___x_3352_);
v___x_3354_ = lean_box(v___x_3332_);
v___x_3355_ = lean_box(v___x_3345_);
v___x_3356_ = lean_box(v___x_3338_);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed), 31, 26);
lean_closure_set(v___f_3357_, 0, v___x_3353_);
lean_closure_set(v___f_3357_, 1, v___x_3354_);
lean_closure_set(v___f_3357_, 2, v_snd_3350_);
lean_closure_set(v___f_3357_, 3, v___x_3316_);
lean_closure_set(v___f_3357_, 4, v___x_3355_);
lean_closure_set(v___f_3357_, 5, v___x_3336_);
lean_closure_set(v___f_3357_, 6, v___x_3317_);
lean_closure_set(v___f_3357_, 7, v_a_3341_);
lean_closure_set(v___f_3357_, 8, v___x_3311_);
lean_closure_set(v___f_3357_, 9, v___x_3313_);
lean_closure_set(v___f_3357_, 10, v___x_3356_);
lean_closure_set(v___f_3357_, 11, v___x_3339_);
lean_closure_set(v___f_3357_, 12, v_params_3318_);
lean_closure_set(v___f_3357_, 13, v_args_3324_);
lean_closure_set(v___f_3357_, 14, v_a_3319_);
lean_closure_set(v___f_3357_, 15, v___x_3320_);
lean_closure_set(v___f_3357_, 16, v___x_3321_);
lean_closure_set(v___f_3357_, 17, v___f_3346_);
lean_closure_set(v___f_3357_, 18, v___x_3344_);
lean_closure_set(v___f_3357_, 19, v___x_3322_);
lean_closure_set(v___f_3357_, 20, v_numIndices_3314_);
lean_closure_set(v___f_3357_, 21, v_goalType_3325_);
lean_closure_set(v___f_3357_, 22, v___x_3352_);
lean_closure_set(v___f_3357_, 23, v___x_3351_);
lean_closure_set(v___f_3357_, 24, v_fst_3349_);
lean_closure_set(v___f_3357_, 25, v___x_3323_);
v___x_3358_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3350_, v___f_3357_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3358_;
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_a_3341_);
lean_dec(v___x_3336_);
lean_dec_ref(v_goalType_3325_);
lean_dec_ref(v_args_3324_);
lean_dec(v___x_3322_);
lean_dec_ref(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_a_3319_);
lean_dec_ref(v_params_3318_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3316_);
lean_dec(v_numIndices_3314_);
lean_dec(v___x_3313_);
lean_dec(v___x_3311_);
v_a_3359_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3347_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3347_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec(v___x_3336_);
lean_dec_ref(v_goalType_3325_);
lean_dec_ref(v_args_3324_);
lean_dec(v___x_3322_);
lean_dec_ref(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_a_3319_);
lean_dec_ref(v_params_3318_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3316_);
lean_dec(v_numIndices_3314_);
lean_dec(v___x_3313_);
lean_dec(v___x_3311_);
v_a_3367_ = lean_ctor_get(v___x_3340_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3340_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3340_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3340_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
lean_dec_ref(v_goalType_3325_);
lean_dec_ref(v_args_3324_);
lean_dec(v___x_3322_);
lean_dec_ref(v___x_3321_);
lean_dec(v___x_3320_);
lean_dec_ref(v_a_3319_);
lean_dec_ref(v_params_3318_);
lean_dec_ref(v___x_3317_);
lean_dec_ref(v___x_3316_);
lean_dec(v_numIndices_3314_);
lean_dec(v___x_3313_);
lean_dec(v___x_3311_);
v___x_3375_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3376_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3375_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
return v___x_3376_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object** _args){
lean_object* v___x_3377_ = _args[0];
lean_object* v_a_3378_ = _args[1];
lean_object* v___x_3379_ = _args[2];
lean_object* v_numIndices_3380_ = _args[3];
lean_object* v___x_3381_ = _args[4];
lean_object* v___x_3382_ = _args[5];
lean_object* v___x_3383_ = _args[6];
lean_object* v_params_3384_ = _args[7];
lean_object* v_a_3385_ = _args[8];
lean_object* v___x_3386_ = _args[9];
lean_object* v___x_3387_ = _args[10];
lean_object* v___x_3388_ = _args[11];
lean_object* v___x_3389_ = _args[12];
lean_object* v_args_3390_ = _args[13];
lean_object* v_goalType_3391_ = _args[14];
lean_object* v___y_3392_ = _args[15];
lean_object* v___y_3393_ = _args[16];
lean_object* v___y_3394_ = _args[17];
lean_object* v___y_3395_ = _args[18];
lean_object* v___y_3396_ = _args[19];
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3377_, v_a_3378_, v___x_3379_, v_numIndices_3380_, v___x_3381_, v___x_3382_, v___x_3383_, v_params_3384_, v_a_3385_, v___x_3386_, v___x_3387_, v___x_3388_, v___x_3389_, v_args_3390_, v_goalType_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___x_3381_);
lean_dec_ref(v_a_3378_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; lean_object* v_env_3405_; uint8_t v___x_3406_; lean_object* v___x_3407_; 
v___x_3404_ = lean_st_ref_get(v___y_3402_);
v_env_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc_ref(v_env_3405_);
lean_dec(v___x_3404_);
v___x_3406_ = 0;
lean_inc(v_constName_3398_);
v___x_3407_ = l_Lean_Environment_findConstVal_x3f(v_env_3405_, v_constName_3398_, v___x_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3408_;
}
else
{
lean_object* v_val_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec(v_constName_3398_);
v_val_3409_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3407_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_val_3409_);
lean_dec(v___x_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
lean_ctor_set_tag(v___x_3411_, 0);
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_val_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3430_; 
lean_inc(v_constName_3424_);
v___x_3430_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3442_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3433_ = v___x_3430_;
v_isShared_3434_ = v_isSharedCheck_3442_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v___x_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3442_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_levelParams_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3440_; 
v_levelParams_3435_ = lean_ctor_get(v_a_3431_, 1);
lean_inc(v_levelParams_3435_);
lean_dec(v_a_3431_);
v___x_3436_ = lean_box(0);
v___x_3437_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3435_, v___x_3436_);
v___x_3438_ = l_Lean_mkConst(v_constName_3424_, v___x_3437_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3438_);
v___x_3440_ = v___x_3433_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3438_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3450_; 
lean_dec(v_constName_3424_);
v_a_3443_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3445_ = v___x_3430_;
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3430_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3450_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3451_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v___y_3460_, lean_object* v_levels_3461_, lean_object* v_params_3462_, lean_object* v_predicates_3463_, lean_object* v_as_3464_, size_t v_sz_3465_, size_t v_i_3466_, lean_object* v_b_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
uint8_t v___x_3473_; 
v___x_3473_ = lean_usize_dec_lt(v_i_3466_, v_sz_3465_);
if (v___x_3473_ == 0)
{
lean_object* v___x_3474_; 
lean_dec_ref(v_params_3462_);
lean_dec(v_levels_3461_);
lean_dec_ref(v___y_3460_);
v___x_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3474_, 0, v_b_3467_);
return v___x_3474_;
}
else
{
lean_object* v_a_3475_; lean_object* v_toConstantVal_3476_; lean_object* v_numParams_3477_; lean_object* v_numIndices_3478_; lean_object* v_name_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___f_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_a_3475_ = lean_array_uget_borrowed(v_as_3464_, v_i_3466_);
v_toConstantVal_3476_ = lean_ctor_get(v_a_3475_, 0);
v_numParams_3477_ = lean_ctor_get(v_a_3475_, 1);
v_numIndices_3478_ = lean_ctor_get(v_a_3475_, 2);
v_name_3479_ = lean_ctor_get(v_toConstantVal_3476_, 0);
v___x_3480_ = lean_unsigned_to_nat(0u);
v___x_3481_ = lean_box(0);
v___x_3482_ = lean_box(0);
lean_inc_ref(v_params_3462_);
lean_inc(v_levels_3461_);
lean_inc_ref(v___y_3460_);
lean_inc_n(v_name_3479_, 2);
lean_inc(v_numParams_3477_);
v___f_3483_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3483_, 0, v_numParams_3477_);
lean_closure_set(v___f_3483_, 1, v_name_3479_);
lean_closure_set(v___f_3483_, 2, v___y_3460_);
lean_closure_set(v___f_3483_, 3, v___x_3480_);
lean_closure_set(v___f_3483_, 4, v_levels_3461_);
lean_closure_set(v___f_3483_, 5, v_params_3462_);
v___x_3484_ = l_Lean_mkCasesOnName(v_name_3479_);
lean_inc(v___x_3484_);
v___x_3485_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3484_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v___x_3487_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3484_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v___x_3487_, 1);
lean_inc_ref(v_params_3462_);
v___x_3489_ = l_Array_append___redArg(v_params_3462_, v_predicates_3463_);
v___x_3490_ = l_Lean_mkAppN(v_a_3488_, v___x_3489_);
lean_dec_ref(v___x_3489_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc_ref(v___x_3490_);
v___x_3491_ = lean_infer_type(v___x_3490_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = lean_replace_expr(v___f_3483_, v_a_3492_);
lean_dec(v_a_3492_);
lean_dec_ref(v___f_3483_);
lean_inc(v___y_3471_);
lean_inc_ref(v___y_3470_);
lean_inc(v___y_3469_);
lean_inc_ref(v___y_3468_);
lean_inc_ref(v___x_3490_);
v___x_3494_ = lean_infer_type(v___x_3490_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___f_3502_; uint8_t v___x_3503_; lean_object* v___x_3504_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
lean_inc(v_name_3479_);
v___x_3496_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3479_);
v___x_3497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3496_);
v___x_3498_ = l_Lean_Name_append(v___x_3496_, v___x_3497_);
lean_inc(v_levels_3461_);
v___x_3499_ = l_Lean_mkConst(v___x_3498_, v_levels_3461_);
v___x_3500_ = lean_unsigned_to_nat(1u);
v___x_3501_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3493_);
lean_inc_ref(v_params_3462_);
lean_inc(v_numIndices_3478_);
v___f_3502_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed), 20, 13);
lean_closure_set(v___f_3502_, 0, v___x_3500_);
lean_closure_set(v___f_3502_, 1, v_a_3495_);
lean_closure_set(v___f_3502_, 2, v___x_3480_);
lean_closure_set(v___f_3502_, 3, v_numIndices_3478_);
lean_closure_set(v___f_3502_, 4, v___x_3481_);
lean_closure_set(v___f_3502_, 5, v___x_3499_);
lean_closure_set(v___f_3502_, 6, v___x_3490_);
lean_closure_set(v___f_3502_, 7, v_params_3462_);
lean_closure_set(v___f_3502_, 8, v_a_3486_);
lean_closure_set(v___f_3502_, 9, v___x_3496_);
lean_closure_set(v___f_3502_, 10, v___x_3493_);
lean_closure_set(v___f_3502_, 11, v___x_3501_);
lean_closure_set(v___f_3502_, 12, v___x_3482_);
v___x_3503_ = 0;
v___x_3504_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_3493_, v___x_3501_, v___f_3502_, v___x_3503_, v___x_3503_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
if (lean_obj_tag(v___x_3504_) == 0)
{
size_t v___x_3505_; size_t v___x_3506_; 
lean_dec_ref_known(v___x_3504_, 1);
v___x_3505_ = ((size_t)1ULL);
v___x_3506_ = lean_usize_add(v_i_3466_, v___x_3505_);
v_i_3466_ = v___x_3506_;
v_b_3467_ = v___x_3482_;
goto _start;
}
else
{
lean_dec_ref(v_params_3462_);
lean_dec(v_levels_3461_);
lean_dec_ref(v___y_3460_);
return v___x_3504_;
}
}
else
{
lean_object* v_a_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v___x_3493_);
lean_dec_ref(v___x_3490_);
lean_dec(v_a_3486_);
lean_dec_ref(v_params_3462_);
lean_dec(v_levels_3461_);
lean_dec_ref(v___y_3460_);
v_a_3508_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3510_ = v___x_3494_;
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_a_3508_);
lean_dec(v___x_3494_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3515_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
lean_object* v___x_3513_; 
if (v_isShared_3511_ == 0)
{
v___x_3513_ = v___x_3510_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_a_3508_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec_ref(v___x_3490_);
lean_dec(v_a_3486_);
lean_dec_ref(v___f_3483_);
lean_dec_ref(v_params_3462_);
lean_dec(v_levels_3461_);
lean_dec_ref(v___y_3460_);
v_a_3516_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3491_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3491_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_a_3516_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_dec(v_a_3486_);
lean_dec_ref(v___f_3483_);
lean_dec_ref(v_params_3462_);
lean_dec(v_levels_3461_);
lean_dec_ref(v___y_3460_);
v_a_3524_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3487_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3487_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v___x_3484_);
lean_dec_ref(v___f_3483_);
lean_dec_ref(v_params_3462_);
lean_dec(v_levels_3461_);
lean_dec_ref(v___y_3460_);
v_a_3532_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3485_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3485_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v___y_3540_, lean_object* v_levels_3541_, lean_object* v_params_3542_, lean_object* v_predicates_3543_, lean_object* v_as_3544_, lean_object* v_sz_3545_, lean_object* v_i_3546_, lean_object* v_b_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
size_t v_sz_boxed_3553_; size_t v_i_boxed_3554_; lean_object* v_res_3555_; 
v_sz_boxed_3553_ = lean_unbox_usize(v_sz_3545_);
lean_dec(v_sz_3545_);
v_i_boxed_3554_ = lean_unbox_usize(v_i_3546_);
lean_dec(v_i_3546_);
v_res_3555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3540_, v_levels_3541_, v_params_3542_, v_predicates_3543_, v_as_3544_, v_sz_boxed_3553_, v_i_boxed_3554_, v_b_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec_ref(v_as_3544_);
lean_dec_ref(v_predicates_3543_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3556_, size_t v_sz_3557_, size_t v_i_3558_, lean_object* v_bs_3559_){
_start:
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_usize_dec_lt(v_i_3558_, v_sz_3557_);
if (v___x_3560_ == 0)
{
lean_dec(v_levels_3556_);
return v_bs_3559_;
}
else
{
lean_object* v_v_3561_; lean_object* v_toConstantVal_3562_; lean_object* v_name_3563_; lean_object* v___x_3564_; lean_object* v_bs_x27_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; size_t v___x_3568_; size_t v___x_3569_; lean_object* v___x_3570_; 
v_v_3561_ = lean_array_uget_borrowed(v_bs_3559_, v_i_3558_);
v_toConstantVal_3562_ = lean_ctor_get(v_v_3561_, 0);
v_name_3563_ = lean_ctor_get(v_toConstantVal_3562_, 0);
lean_inc(v_name_3563_);
v___x_3564_ = lean_unsigned_to_nat(0u);
v_bs_x27_3565_ = lean_array_uset(v_bs_3559_, v_i_3558_, v___x_3564_);
v___x_3566_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3563_);
lean_inc(v_levels_3556_);
v___x_3567_ = l_Lean_mkConst(v___x_3566_, v_levels_3556_);
v___x_3568_ = ((size_t)1ULL);
v___x_3569_ = lean_usize_add(v_i_3558_, v___x_3568_);
v___x_3570_ = lean_array_uset(v_bs_x27_3565_, v_i_3558_, v___x_3567_);
v_i_3558_ = v___x_3569_;
v_bs_3559_ = v___x_3570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3572_, lean_object* v_sz_3573_, lean_object* v_i_3574_, lean_object* v_bs_3575_){
_start:
{
size_t v_sz_boxed_3576_; size_t v_i_boxed_3577_; lean_object* v_res_3578_; 
v_sz_boxed_3576_ = lean_unbox_usize(v_sz_3573_);
lean_dec(v_sz_3573_);
v_i_boxed_3577_ = lean_unbox_usize(v_i_3574_);
lean_dec(v_i_3574_);
v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3572_, v_sz_boxed_3576_, v_i_boxed_3577_, v_bs_3575_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3579_, lean_object* v_levels_3580_, lean_object* v___y_3581_, lean_object* v_params_3582_, lean_object* v_x_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_){
_start:
{
size_t v_sz_3589_; size_t v___x_3590_; lean_object* v_predicates_3591_; size_t v_sz_3592_; lean_object* v_predicates_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v_sz_3589_ = lean_array_size(v_infos_3579_);
v___x_3590_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3579_);
lean_inc(v_levels_3580_);
v_predicates_3591_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3580_, v_sz_3589_, v___x_3590_, v_infos_3579_);
v_sz_3592_ = lean_array_size(v_predicates_3591_);
v_predicates_3593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3582_, v_sz_3592_, v___x_3590_, v_predicates_3591_);
v___x_3594_ = lean_box(0);
v___x_3595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3581_, v_levels_3580_, v_params_3582_, v_predicates_3593_, v_infos_3579_, v_sz_3589_, v___x_3590_, v___x_3594_, v___y_3584_, v___y_3585_, v___y_3586_, v___y_3587_);
lean_dec_ref(v_infos_3579_);
lean_dec_ref(v_predicates_3593_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3602_ == 0)
{
lean_object* v_unused_3603_; 
v_unused_3603_ = lean_ctor_get(v___x_3595_, 0);
lean_dec(v_unused_3603_);
v___x_3597_ = v___x_3595_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_dec(v___x_3595_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
lean_ctor_set(v___x_3597_, 0, v___x_3594_);
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3594_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
else
{
return v___x_3595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3604_, lean_object* v_levels_3605_, lean_object* v___y_3606_, lean_object* v_params_3607_, lean_object* v_x_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3604_, v_levels_3605_, v___y_3606_, v_params_3607_, v_x_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec_ref(v_x_3608_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3615_, size_t v_i_3616_, size_t v_stop_3617_, lean_object* v_b_3618_){
_start:
{
uint8_t v___x_3619_; 
v___x_3619_ = lean_usize_dec_eq(v_i_3616_, v_stop_3617_);
if (v___x_3619_ == 0)
{
lean_object* v___x_3620_; lean_object* v_ctors_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; size_t v___x_3624_; size_t v___x_3625_; 
v___x_3620_ = lean_array_uget_borrowed(v_as_3615_, v_i_3616_);
v_ctors_3621_ = lean_ctor_get(v___x_3620_, 4);
lean_inc(v_ctors_3621_);
v___x_3622_ = lean_array_mk(v_ctors_3621_);
v___x_3623_ = l_Array_append___redArg(v_b_3618_, v___x_3622_);
lean_dec_ref(v___x_3622_);
v___x_3624_ = ((size_t)1ULL);
v___x_3625_ = lean_usize_add(v_i_3616_, v___x_3624_);
v_i_3616_ = v___x_3625_;
v_b_3618_ = v___x_3623_;
goto _start;
}
else
{
return v_b_3618_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3627_, lean_object* v_i_3628_, lean_object* v_stop_3629_, lean_object* v_b_3630_){
_start:
{
size_t v_i_boxed_3631_; size_t v_stop_boxed_3632_; lean_object* v_res_3633_; 
v_i_boxed_3631_ = lean_unbox_usize(v_i_3628_);
lean_dec(v_i_3628_);
v_stop_boxed_3632_ = lean_unbox_usize(v_stop_3629_);
lean_dec(v_stop_3629_);
v_res_3633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3627_, v_i_boxed_3631_, v_stop_boxed_3632_, v_b_3630_);
lean_dec_ref(v_as_3627_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_toConstantVal_3645_; lean_object* v_numParams_3646_; lean_object* v_levelParams_3647_; lean_object* v_type_3648_; lean_object* v___x_3649_; lean_object* v_levels_3650_; lean_object* v___y_3652_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3642_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3643_ = lean_unsigned_to_nat(0u);
v___x_3644_ = lean_array_get_borrowed(v___x_3642_, v_infos_3636_, v___x_3643_);
v_toConstantVal_3645_ = lean_ctor_get(v___x_3644_, 0);
v_numParams_3646_ = lean_ctor_get(v___x_3644_, 1);
lean_inc(v_numParams_3646_);
v_levelParams_3647_ = lean_ctor_get(v_toConstantVal_3645_, 1);
v_type_3648_ = lean_ctor_get(v_toConstantVal_3645_, 2);
lean_inc_ref(v_type_3648_);
v___x_3649_ = lean_box(0);
lean_inc(v_levelParams_3647_);
v_levels_3650_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3647_, v___x_3649_);
v___x_3659_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3660_ = lean_array_get_size(v_infos_3636_);
v___x_3661_ = lean_nat_dec_lt(v___x_3643_, v___x_3660_);
if (v___x_3661_ == 0)
{
v___y_3652_ = v___x_3659_;
goto v___jp_3651_;
}
else
{
size_t v___x_3662_; size_t v___x_3663_; lean_object* v___x_3664_; 
v___x_3662_ = ((size_t)0ULL);
v___x_3663_ = lean_usize_of_nat(v___x_3660_);
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3636_, v___x_3662_, v___x_3663_, v___x_3659_);
v___y_3652_ = v___x_3664_;
goto v___jp_3651_;
}
v___jp_3651_:
{
lean_object* v___f_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; 
lean_inc_ref(v_infos_3636_);
v___f_3653_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3653_, 0, v_infos_3636_);
lean_closure_set(v___f_3653_, 1, v_levels_3650_);
lean_closure_set(v___f_3653_, 2, v___y_3652_);
v___x_3654_ = lean_array_get_size(v_infos_3636_);
lean_dec_ref(v_infos_3636_);
v___x_3655_ = lean_nat_sub(v_numParams_3646_, v___x_3654_);
lean_dec(v_numParams_3646_);
v___x_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3655_);
v___x_3657_ = 0;
v___x_3658_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_3648_, v___x_3656_, v___f_3653_, v___x_3657_, v___x_3657_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
return v___x_3658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
lean_dec(v_a_3667_);
lean_dec_ref(v_a_3666_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3672_, lean_object* v_constName_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3680_, lean_object* v_constName_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3680_, v_constName_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3688_, lean_object* v_ref_3689_, lean_object* v_constName_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v___x_3696_; 
v___x_3696_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3689_, v_constName_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3697_, lean_object* v_ref_3698_, lean_object* v_constName_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3697_, v_ref_3698_, v_constName_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v_ref_3698_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3706_, lean_object* v_ref_3707_, lean_object* v_msg_3708_, lean_object* v_declHint_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3707_, v_msg_3708_, v_declHint_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3716_, lean_object* v_ref_3717_, lean_object* v_msg_3718_, lean_object* v_declHint_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3716_, v_ref_3717_, v_msg_3718_, v_declHint_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v_ref_3717_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3726_, lean_object* v_declHint_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3726_, v_declHint_3727_, v___y_3731_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3734_, lean_object* v_declHint_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3734_, v_declHint_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3742_, lean_object* v_ref_3743_, lean_object* v_msg_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3743_, v_msg_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3751_, lean_object* v_ref_3752_, lean_object* v_msg_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3751_, v_ref_3752_, v_msg_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v_ref_3752_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3763_, lean_object* v___x_3764_, lean_object* v_params_3765_, size_t v_sz_3766_, size_t v_i_3767_, lean_object* v_bs_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
uint8_t v___x_3774_; 
v___x_3774_ = lean_usize_dec_lt(v_i_3767_, v_sz_3766_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; 
lean_dec_ref(v_params_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3763_);
v___x_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_bs_3768_);
return v___x_3775_;
}
else
{
lean_object* v_v_3776_; lean_object* v_toConstantVal_3777_; lean_object* v_name_3778_; lean_object* v___x_3779_; lean_object* v_bs_x27_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v_v_3776_ = lean_array_uget_borrowed(v_bs_3768_, v_i_3767_);
v_toConstantVal_3777_ = lean_ctor_get(v_v_3776_, 0);
v_name_3778_ = lean_ctor_get(v_toConstantVal_3777_, 0);
lean_inc(v_name_3778_);
v___x_3779_ = lean_unsigned_to_nat(0u);
v_bs_x27_3780_ = lean_array_uset(v_bs_3768_, v_i_3767_, v___x_3779_);
v___x_3781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3782_ = l_Lean_Name_append(v_name_3778_, v___x_3781_);
lean_inc(v___x_3763_);
v___x_3783_ = l_Lean_mkConst(v___x_3782_, v___x_3763_);
v___x_3784_ = l_Lean_Meta_unfoldDefinition(v___x_3783_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; size_t v_sz_3786_; size_t v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; uint8_t v___x_3792_; lean_object* v___x_3793_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
v_sz_3786_ = lean_array_size(v___x_3764_);
v___x_3787_ = ((size_t)0ULL);
lean_inc_ref(v___x_3764_);
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3765_, v_sz_3786_, v___x_3787_, v___x_3764_);
lean_inc_ref(v_params_3765_);
v___x_3789_ = l_Array_append___redArg(v_params_3765_, v___x_3788_);
lean_dec_ref(v___x_3788_);
v___x_3790_ = l_Lean_mkAppN(v_a_3785_, v___x_3789_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = 0;
v___x_3792_ = 1;
v___x_3793_ = l_Lean_Meta_mkLambdaFVars(v_params_3765_, v___x_3790_, v___x_3791_, v___x_3774_, v___x_3791_, v___x_3774_, v___x_3792_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; size_t v___x_3795_; size_t v___x_3796_; lean_object* v___x_3797_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref_known(v___x_3793_, 1);
v___x_3795_ = ((size_t)1ULL);
v___x_3796_ = lean_usize_add(v_i_3767_, v___x_3795_);
v___x_3797_ = lean_array_uset(v_bs_x27_3780_, v_i_3767_, v_a_3794_);
v_i_3767_ = v___x_3796_;
v_bs_3768_ = v___x_3797_;
goto _start;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_bs_x27_3780_);
lean_dec_ref(v_params_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3763_);
v_a_3799_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3793_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3793_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_object* v_a_3807_; lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3814_; 
lean_dec_ref(v_bs_x27_3780_);
lean_dec_ref(v_params_3765_);
lean_dec_ref(v___x_3764_);
lean_dec(v___x_3763_);
v_a_3807_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3809_ = v___x_3784_;
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
else
{
lean_inc(v_a_3807_);
lean_dec(v___x_3784_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3814_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3812_; 
if (v_isShared_3810_ == 0)
{
v___x_3812_ = v___x_3809_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3815_, lean_object* v___x_3816_, lean_object* v_params_3817_, lean_object* v_sz_3818_, lean_object* v_i_3819_, lean_object* v_bs_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
size_t v_sz_boxed_3826_; size_t v_i_boxed_3827_; lean_object* v_res_3828_; 
v_sz_boxed_3826_ = lean_unbox_usize(v_sz_3818_);
lean_dec(v_sz_3818_);
v_i_boxed_3827_ = lean_unbox_usize(v_i_3819_);
lean_dec(v_i_3819_);
v_res_3828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3815_, v___x_3816_, v_params_3817_, v_sz_boxed_3826_, v_i_boxed_3827_, v_bs_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3829_, lean_object* v___x_3830_, size_t v_sz_3831_, size_t v___x_3832_, lean_object* v_a_3833_, lean_object* v_params_3834_, lean_object* v_x_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; 
v___x_3843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3829_, v___x_3830_, v_params_3834_, v_sz_3831_, v___x_3832_, v_a_3833_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3844_, lean_object* v___x_3845_, lean_object* v_sz_3846_, lean_object* v___x_3847_, lean_object* v_a_3848_, lean_object* v_params_3849_, lean_object* v_x_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
size_t v_sz_boxed_3858_; size_t v___x_5774__boxed_3859_; lean_object* v_res_3860_; 
v_sz_boxed_3858_ = lean_unbox_usize(v_sz_3846_);
lean_dec(v_sz_3846_);
v___x_5774__boxed_3859_ = lean_unbox_usize(v___x_3847_);
lean_dec(v___x_3847_);
v_res_3860_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3844_, v___x_3845_, v_sz_boxed_3858_, v___x_5774__boxed_3859_, v_a_3848_, v_params_3849_, v_x_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
lean_dec(v___y_3852_);
lean_dec_ref(v___y_3851_);
lean_dec_ref(v_x_3850_);
return v_res_3860_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(lean_object* v___x_3861_, uint8_t v___x_3862_, lean_object* v_attr_3863_){
_start:
{
lean_object* v_name_3864_; lean_object* v___x_3865_; 
v_name_3864_ = lean_ctor_get(v_attr_3863_, 0);
lean_inc(v_name_3864_);
lean_dec_ref(v_attr_3863_);
v___x_3865_ = l_Lean_getAttributeImpl(v___x_3861_, v_name_3864_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_dec_ref_known(v___x_3865_, 1);
return v___x_3862_;
}
else
{
lean_object* v_a_3866_; lean_object* v_toAttributeImplCore_3867_; uint8_t v_applicationTime_3868_; uint8_t v___x_3869_; uint8_t v___x_3870_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref_known(v___x_3865_, 1);
v_toAttributeImplCore_3867_ = lean_ctor_get(v_a_3866_, 0);
lean_inc_ref(v_toAttributeImplCore_3867_);
lean_dec(v_a_3866_);
v_applicationTime_3868_ = lean_ctor_get_uint8(v_toAttributeImplCore_3867_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_3867_);
v___x_3869_ = 1;
v___x_3870_ = l_Lean_instBEqAttributeApplicationTime_beq(v_applicationTime_3868_, v___x_3869_);
if (v___x_3870_ == 0)
{
return v___x_3862_;
}
else
{
uint8_t v___x_3871_; 
v___x_3871_ = 0;
return v___x_3871_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed(lean_object* v___x_3872_, lean_object* v___x_3873_, lean_object* v_attr_3874_){
_start:
{
uint8_t v___x_5811__boxed_3875_; uint8_t v_res_3876_; lean_object* v_r_3877_; 
v___x_5811__boxed_3875_ = lean_unbox(v___x_3873_);
v_res_3876_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(v___x_3872_, v___x_5811__boxed_3875_, v_attr_3874_);
v_r_3877_ = lean_box(v_res_3876_);
return v_r_3877_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = l_Lean_instInhabitedExpr;
v___x_3879_ = lean_box(0);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v___x_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3881_, lean_object* v___x_3882_, lean_object* v_a_3883_, lean_object* v___x_3884_, size_t v_sz_3885_, size_t v_i_3886_, lean_object* v_bs_3887_){
_start:
{
uint8_t v___x_3888_; 
v___x_3888_ = lean_usize_dec_lt(v_i_3886_, v_sz_3885_);
if (v___x_3888_ == 0)
{
lean_dec(v___x_3884_);
lean_dec_ref(v___x_3882_);
return v_bs_3887_;
}
else
{
lean_object* v___x_3889_; lean_object* v_v_3890_; lean_object* v___x_3891_; lean_object* v_bs_x27_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v_modifiers_3895_; lean_object* v_ref_3896_; uint8_t v_isGreatest_3897_; lean_object* v_monotonicity_x3f_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3940_; 
v___x_3889_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v_v_3890_ = lean_array_uget(v_bs_3887_, v_i_3886_);
v___x_3891_ = lean_unsigned_to_nat(0u);
v_bs_x27_3892_ = lean_array_uset(v_bs_3887_, v_i_3886_, v___x_3891_);
v___x_3893_ = lean_usize_to_nat(v_i_3886_);
v___x_3894_ = lean_array_get(v___x_3889_, v_coinductiveElabData_3881_, v___x_3893_);
v_modifiers_3895_ = lean_ctor_get(v___x_3894_, 3);
v_ref_3896_ = lean_ctor_get(v___x_3894_, 2);
v_isGreatest_3897_ = lean_ctor_get_uint8(v___x_3894_, sizeof(void*)*6);
v_monotonicity_x3f_3898_ = lean_ctor_get(v___x_3894_, 5);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; lean_object* v_unused_3942_; lean_object* v_unused_3943_; 
v_unused_3941_ = lean_ctor_get(v___x_3894_, 4);
lean_dec(v_unused_3941_);
v_unused_3942_ = lean_ctor_get(v___x_3894_, 1);
lean_dec(v_unused_3942_);
v_unused_3943_ = lean_ctor_get(v___x_3894_, 0);
lean_dec(v_unused_3943_);
v___x_3900_ = v___x_3894_;
v_isShared_3901_ = v_isSharedCheck_3940_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_monotonicity_x3f_3898_);
lean_inc(v_modifiers_3895_);
lean_inc(v_ref_3896_);
lean_dec(v___x_3894_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3940_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_stx_3902_; uint8_t v_visibility_3903_; uint8_t v_isProtected_3904_; uint8_t v_computeKind_3905_; uint8_t v_recKind_3906_; uint8_t v_isUnsafe_3907_; lean_object* v_attrs_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3938_; 
v_stx_3902_ = lean_ctor_get(v_modifiers_3895_, 0);
v_visibility_3903_ = lean_ctor_get_uint8(v_modifiers_3895_, sizeof(void*)*3);
v_isProtected_3904_ = lean_ctor_get_uint8(v_modifiers_3895_, sizeof(void*)*3 + 1);
v_computeKind_3905_ = lean_ctor_get_uint8(v_modifiers_3895_, sizeof(void*)*3 + 2);
v_recKind_3906_ = lean_ctor_get_uint8(v_modifiers_3895_, sizeof(void*)*3 + 3);
v_isUnsafe_3907_ = lean_ctor_get_uint8(v_modifiers_3895_, sizeof(void*)*3 + 4);
v_attrs_3908_ = lean_ctor_get(v_modifiers_3895_, 2);
v_isSharedCheck_3938_ = !lean_is_exclusive(v_modifiers_3895_);
if (v_isSharedCheck_3938_ == 0)
{
lean_object* v_unused_3939_; 
v_unused_3939_ = lean_ctor_get(v_modifiers_3895_, 1);
lean_dec(v_unused_3939_);
v___x_3910_ = v_modifiers_3895_;
v_isShared_3911_ = v_isSharedCheck_3938_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_attrs_3908_);
lean_inc(v_stx_3902_);
lean_dec(v_modifiers_3895_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3938_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v_fst_3914_; lean_object* v_snd_3915_; lean_object* v___x_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3912_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3913_ = lean_array_get_borrowed(v___x_3912_, v_a_3883_, v___x_3893_);
lean_dec(v___x_3893_);
v_fst_3914_ = lean_ctor_get(v___x_3913_, 0);
v_snd_3915_ = lean_ctor_get(v___x_3913_, 1);
v___x_3916_ = lean_box(v___x_3888_);
lean_inc_ref(v___x_3882_);
v___f_3917_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3917_, 0, v___x_3882_);
lean_closure_set(v___f_3917_, 1, v___x_3916_);
v___x_3918_ = lean_box(0);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 1, v___x_3918_);
v___x_3920_ = v___x_3910_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_stx_3902_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3937_, 2, v_attrs_3908_);
lean_ctor_set_uint8(v_reuseFailAlloc_3937_, sizeof(void*)*3, v_visibility_3903_);
lean_ctor_set_uint8(v_reuseFailAlloc_3937_, sizeof(void*)*3 + 1, v_isProtected_3904_);
lean_ctor_set_uint8(v_reuseFailAlloc_3937_, sizeof(void*)*3 + 2, v_computeKind_3905_);
lean_ctor_set_uint8(v_reuseFailAlloc_3937_, sizeof(void*)*3 + 3, v_recKind_3906_);
lean_ctor_set_uint8(v_reuseFailAlloc_3937_, sizeof(void*)*3 + 4, v_isUnsafe_3907_);
v___x_3920_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
lean_object* v___x_3921_; uint8_t v___x_3922_; uint8_t v___y_3924_; 
v___x_3921_ = l_Lean_Elab_Modifiers_filterAttrs(v___x_3920_, v___f_3917_);
v___x_3922_ = 0;
if (v_isGreatest_3897_ == 0)
{
uint8_t v___x_3935_; 
v___x_3935_ = 2;
v___y_3924_ = v___x_3935_;
goto v___jp_3923_;
}
else
{
uint8_t v___x_3936_; 
v___x_3936_ = 1;
v___y_3924_ = v___x_3936_;
goto v___jp_3923_;
}
v___jp_3923_:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_inc_n(v_ref_3896_, 2);
v___x_3925_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3925_, 0, v_ref_3896_);
lean_ctor_set(v___x_3925_, 1, v_monotonicity_x3f_3898_);
lean_ctor_set_uint8(v___x_3925_, sizeof(void*)*2, v___y_3924_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 5, v___x_3891_);
lean_ctor_set(v___x_3900_, 4, v___x_3918_);
lean_ctor_set(v___x_3900_, 3, v___x_3926_);
lean_ctor_set(v___x_3900_, 2, v___x_3918_);
lean_ctor_set(v___x_3900_, 1, v___x_3918_);
lean_ctor_set(v___x_3900_, 0, v_ref_3896_);
v___x_3928_ = v___x_3900_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_ref_3896_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3934_, 2, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3934_, 3, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3934_, 4, v___x_3918_);
lean_ctor_set(v_reuseFailAlloc_3934_, 5, v___x_3891_);
v___x_3928_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; size_t v___x_3930_; size_t v___x_3931_; lean_object* v___x_3932_; 
lean_ctor_set_uint8(v___x_3928_, sizeof(void*)*6, v___x_3888_);
lean_inc(v_snd_3915_);
lean_inc(v_fst_3914_);
lean_inc(v___x_3884_);
lean_inc(v_ref_3896_);
v___x_3929_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3929_, 0, v_ref_3896_);
lean_ctor_set(v___x_3929_, 1, v___x_3884_);
lean_ctor_set(v___x_3929_, 2, v___x_3921_);
lean_ctor_set(v___x_3929_, 3, v_fst_3914_);
lean_ctor_set(v___x_3929_, 4, v_ref_3896_);
lean_ctor_set(v___x_3929_, 5, v___x_3891_);
lean_ctor_set(v___x_3929_, 6, v_snd_3915_);
lean_ctor_set(v___x_3929_, 7, v_v_3890_);
lean_ctor_set(v___x_3929_, 8, v___x_3928_);
lean_ctor_set_uint8(v___x_3929_, sizeof(void*)*9, v___x_3922_);
v___x_3930_ = ((size_t)1ULL);
v___x_3931_ = lean_usize_add(v_i_3886_, v___x_3930_);
v___x_3932_ = lean_array_uset(v_bs_x27_3892_, v_i_3886_, v___x_3929_);
v_i_3886_ = v___x_3931_;
v_bs_3887_ = v___x_3932_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object* v_coinductiveElabData_3944_, lean_object* v___x_3945_, lean_object* v_a_3946_, lean_object* v___x_3947_, lean_object* v_sz_3948_, lean_object* v_i_3949_, lean_object* v_bs_3950_){
_start:
{
size_t v_sz_boxed_3951_; size_t v_i_boxed_3952_; lean_object* v_res_3953_; 
v_sz_boxed_3951_ = lean_unbox_usize(v_sz_3948_);
lean_dec(v_sz_3948_);
v_i_boxed_3952_ = lean_unbox_usize(v_i_3949_);
lean_dec(v_i_3949_);
v_res_3953_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_3944_, v___x_3945_, v_a_3946_, v___x_3947_, v_sz_boxed_3951_, v_i_boxed_3952_, v_bs_3950_);
lean_dec_ref(v_a_3946_);
lean_dec_ref(v_coinductiveElabData_3944_);
return v_res_3953_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0));
v___x_3956_ = l_Lean_stringToMessageData(v___x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object* v_constName_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
lean_object* v___x_3965_; lean_object* v_env_3966_; lean_object* v___x_3967_; 
v___x_3965_ = lean_st_ref_get(v___y_3963_);
v_env_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc_ref(v_env_3966_);
lean_dec(v___x_3965_);
lean_inc(v_constName_3957_);
v___x_3967_ = l_Lean_isInductiveCore_x3f(v_env_3966_, v_constName_3957_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3968_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_3969_ = 0;
v___x_3970_ = l_Lean_MessageData_ofConstName(v_constName_3957_, v___x_3969_);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3968_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
v___x_3973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3971_);
lean_ctor_set(v___x_3973_, 1, v___x_3972_);
v___x_3974_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_3973_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_);
return v___x_3974_;
}
else
{
lean_object* v_val_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_constName_3957_);
v_val_3975_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3967_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_val_3975_);
lean_dec(v___x_3967_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
lean_ctor_set_tag(v___x_3977_, 0);
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_val_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object* v_constName_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t v_sz_3992_, size_t v_i_3993_, lean_object* v_bs_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
uint8_t v___x_4002_; 
v___x_4002_ = lean_usize_dec_lt(v_i_3993_, v_sz_3992_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; 
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v_bs_3994_);
return v___x_4003_;
}
else
{
lean_object* v_v_4004_; lean_object* v_declName_4005_; lean_object* v___x_4006_; lean_object* v_bs_x27_4007_; lean_object* v___x_4008_; 
v_v_4004_ = lean_array_uget_borrowed(v_bs_3994_, v_i_3993_);
v_declName_4005_ = lean_ctor_get(v_v_4004_, 1);
lean_inc(v_declName_4005_);
v___x_4006_ = lean_unsigned_to_nat(0u);
v_bs_x27_4007_ = lean_array_uset(v_bs_3994_, v_i_3993_, v___x_4006_);
v___x_4008_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_4005_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; size_t v___x_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = ((size_t)1ULL);
v___x_4011_ = lean_usize_add(v_i_3993_, v___x_4010_);
v___x_4012_ = lean_array_uset(v_bs_x27_4007_, v_i_3993_, v_a_4009_);
v_i_3993_ = v___x_4011_;
v_bs_3994_ = v___x_4012_;
goto _start;
}
else
{
lean_object* v_a_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4021_; 
lean_dec_ref(v_bs_x27_4007_);
v_a_4014_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_4016_ = v___x_4008_;
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_a_4014_);
lean_dec(v___x_4008_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4021_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___x_4019_; 
if (v_isShared_4017_ == 0)
{
v___x_4019_ = v___x_4016_;
goto v_reusejp_4018_;
}
else
{
lean_object* v_reuseFailAlloc_4020_; 
v_reuseFailAlloc_4020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4020_, 0, v_a_4014_);
v___x_4019_ = v_reuseFailAlloc_4020_;
goto v_reusejp_4018_;
}
v_reusejp_4018_:
{
return v___x_4019_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object* v_sz_4022_, lean_object* v_i_4023_, lean_object* v_bs_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
size_t v_sz_boxed_4032_; size_t v_i_boxed_4033_; lean_object* v_res_4034_; 
v_sz_boxed_4032_ = lean_unbox_usize(v_sz_4022_);
lean_dec(v_sz_4022_);
v_i_boxed_4033_ = lean_unbox_usize(v_i_4023_);
lean_dec(v_i_4023_);
v_res_4034_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_4032_, v_i_boxed_4033_, v_bs_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object* v_a_4035_, lean_object* v_a_4036_){
_start:
{
if (lean_obj_tag(v_a_4035_) == 0)
{
lean_object* v___x_4037_; 
v___x_4037_ = l_List_reverse___redArg(v_a_4036_);
return v___x_4037_;
}
else
{
lean_object* v_head_4038_; lean_object* v_tail_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4048_; 
v_head_4038_ = lean_ctor_get(v_a_4035_, 0);
v_tail_4039_ = lean_ctor_get(v_a_4035_, 1);
v_isSharedCheck_4048_ = !lean_is_exclusive(v_a_4035_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4041_ = v_a_4035_;
v_isShared_4042_ = v_isSharedCheck_4048_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_tail_4039_);
lean_inc(v_head_4038_);
lean_dec(v_a_4035_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4048_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4043_; lean_object* v___x_4045_; 
v___x_4043_ = l_Lean_MessageData_ofName(v_head_4038_);
if (v_isShared_4042_ == 0)
{
lean_ctor_set(v___x_4041_, 1, v_a_4036_);
lean_ctor_set(v___x_4041_, 0, v___x_4043_);
v___x_4045_ = v___x_4041_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v___x_4043_);
lean_ctor_set(v_reuseFailAlloc_4047_, 1, v_a_4036_);
v___x_4045_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
v_a_4035_ = v_tail_4039_;
v_a_4036_ = v___x_4045_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t v_sz_4049_, size_t v_i_4050_, lean_object* v_bs_4051_){
_start:
{
uint8_t v___x_4052_; 
v___x_4052_ = lean_usize_dec_lt(v_i_4050_, v_sz_4049_);
if (v___x_4052_ == 0)
{
return v_bs_4051_;
}
else
{
lean_object* v_v_4053_; lean_object* v_declName_4054_; lean_object* v___x_4055_; lean_object* v_bs_x27_4056_; size_t v___x_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
v_v_4053_ = lean_array_uget_borrowed(v_bs_4051_, v_i_4050_);
v_declName_4054_ = lean_ctor_get(v_v_4053_, 1);
lean_inc(v_declName_4054_);
v___x_4055_ = lean_unsigned_to_nat(0u);
v_bs_x27_4056_ = lean_array_uset(v_bs_4051_, v_i_4050_, v___x_4055_);
v___x_4057_ = ((size_t)1ULL);
v___x_4058_ = lean_usize_add(v_i_4050_, v___x_4057_);
v___x_4059_ = lean_array_uset(v_bs_x27_4056_, v_i_4050_, v_declName_4054_);
v_i_4050_ = v___x_4058_;
v_bs_4051_ = v___x_4059_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object* v_sz_4061_, lean_object* v_i_4062_, lean_object* v_bs_4063_){
_start:
{
size_t v_sz_boxed_4064_; size_t v_i_boxed_4065_; lean_object* v_res_4066_; 
v_sz_boxed_4064_ = lean_unbox_usize(v_sz_4061_);
lean_dec(v_sz_4061_);
v_i_boxed_4065_ = lean_unbox_usize(v_i_4062_);
lean_dec(v_i_4062_);
v_res_4066_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_4064_, v_i_boxed_4065_, v_bs_4063_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v___x_4067_, lean_object* v___x_4068_, lean_object* v_numParams_4069_, uint8_t v___x_4070_, lean_object* v_args_4071_, lean_object* v_body_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; uint8_t v___x_4087_; lean_object* v___x_4088_; 
lean_inc_ref(v_args_4071_);
v___x_4080_ = l_Array_toSubarray___redArg(v_args_4071_, v___x_4067_, v___x_4068_);
v___x_4081_ = l_Subarray_copy___redArg(v___x_4080_);
v___x_4082_ = lean_array_get_size(v_args_4071_);
v___x_4083_ = l_Array_toSubarray___redArg(v_args_4071_, v_numParams_4069_, v___x_4082_);
v___x_4084_ = l_Subarray_copy___redArg(v___x_4083_);
v___x_4085_ = l_Array_append___redArg(v___x_4081_, v___x_4084_);
lean_dec_ref(v___x_4084_);
v___x_4086_ = 0;
v___x_4087_ = 1;
v___x_4088_ = l_Lean_Meta_mkForallFVars(v___x_4085_, v_body_4072_, v___x_4086_, v___x_4070_, v___x_4070_, v___x_4087_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec_ref(v___x_4085_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v___x_4089_, lean_object* v___x_4090_, lean_object* v_numParams_4091_, lean_object* v___x_4092_, lean_object* v_args_4093_, lean_object* v_body_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
uint8_t v___x_6091__boxed_4102_; lean_object* v_res_4103_; 
v___x_6091__boxed_4102_ = lean_unbox(v___x_4092_);
v_res_4103_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v___x_4089_, v___x_4090_, v_numParams_4091_, v___x_6091__boxed_4102_, v_args_4093_, v_body_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
lean_dec_ref(v___y_4097_);
lean_dec(v___y_4096_);
lean_dec_ref(v___y_4095_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_4104_, size_t v_sz_4105_, size_t v_i_4106_, lean_object* v_bs_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
uint8_t v___x_4115_; 
v___x_4115_ = lean_usize_dec_lt(v_i_4106_, v_sz_4105_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; 
lean_dec(v___x_4104_);
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v_bs_4107_);
return v___x_4116_;
}
else
{
lean_object* v_v_4117_; lean_object* v_toConstantVal_4118_; lean_object* v_numParams_4119_; lean_object* v_name_4120_; lean_object* v_type_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___f_4124_; lean_object* v_bs_x27_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; 
v_v_4117_ = lean_array_uget_borrowed(v_bs_4107_, v_i_4106_);
v_toConstantVal_4118_ = lean_ctor_get(v_v_4117_, 0);
v_numParams_4119_ = lean_ctor_get(v_v_4117_, 1);
v_name_4120_ = lean_ctor_get(v_toConstantVal_4118_, 0);
lean_inc(v_name_4120_);
v_type_4121_ = lean_ctor_get(v_toConstantVal_4118_, 2);
lean_inc_ref(v_type_4121_);
v___x_4122_ = lean_unsigned_to_nat(0u);
v___x_4123_ = lean_box(v___x_4115_);
lean_inc(v_numParams_4119_);
lean_inc(v___x_4104_);
v___f_4124_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4124_, 0, v___x_4122_);
lean_closure_set(v___f_4124_, 1, v___x_4104_);
lean_closure_set(v___f_4124_, 2, v_numParams_4119_);
lean_closure_set(v___f_4124_, 3, v___x_4123_);
v_bs_x27_4125_ = lean_array_uset(v_bs_4107_, v_i_4106_, v___x_4122_);
v___x_4126_ = 0;
v___x_4127_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4121_, v___f_4124_, v___x_4126_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; size_t v___x_4131_; size_t v___x_4132_; lean_object* v___x_4133_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v___x_4129_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4120_);
v___x_4130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
lean_ctor_set(v___x_4130_, 1, v_a_4128_);
v___x_4131_ = ((size_t)1ULL);
v___x_4132_ = lean_usize_add(v_i_4106_, v___x_4131_);
v___x_4133_ = lean_array_uset(v_bs_x27_4125_, v_i_4106_, v___x_4130_);
v_i_4106_ = v___x_4132_;
v_bs_4107_ = v___x_4133_;
goto _start;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v_bs_x27_4125_);
lean_dec(v_name_4120_);
lean_dec(v___x_4104_);
v_a_4135_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4127_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4127_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object* v___x_4143_, lean_object* v_sz_4144_, lean_object* v_i_4145_, lean_object* v_bs_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
size_t v_sz_boxed_4154_; size_t v_i_boxed_4155_; lean_object* v_res_4156_; 
v_sz_boxed_4154_ = lean_unbox_usize(v_sz_4144_);
lean_dec(v_sz_4144_);
v_i_boxed_4155_ = lean_unbox_usize(v_i_4145_);
lean_dec(v_i_4145_);
v_res_4156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4143_, v_sz_boxed_4154_, v_i_boxed_4155_, v_bs_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v___y_4148_);
lean_dec_ref(v___y_4147_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object* v___x_4157_, size_t v_sz_4158_, size_t v_i_4159_, lean_object* v_bs_4160_){
_start:
{
uint8_t v___x_4161_; 
v___x_4161_ = lean_usize_dec_lt(v_i_4159_, v_sz_4158_);
if (v___x_4161_ == 0)
{
lean_dec(v___x_4157_);
return v_bs_4160_;
}
else
{
lean_object* v_v_4162_; lean_object* v_fst_4163_; lean_object* v___x_4164_; lean_object* v_bs_x27_4165_; lean_object* v___x_4166_; size_t v___x_4167_; size_t v___x_4168_; lean_object* v___x_4169_; 
v_v_4162_ = lean_array_uget_borrowed(v_bs_4160_, v_i_4159_);
v_fst_4163_ = lean_ctor_get(v_v_4162_, 0);
lean_inc(v_fst_4163_);
v___x_4164_ = lean_unsigned_to_nat(0u);
v_bs_x27_4165_ = lean_array_uset(v_bs_4160_, v_i_4159_, v___x_4164_);
lean_inc(v___x_4157_);
v___x_4166_ = l_Lean_mkConst(v_fst_4163_, v___x_4157_);
v___x_4167_ = ((size_t)1ULL);
v___x_4168_ = lean_usize_add(v_i_4159_, v___x_4167_);
v___x_4169_ = lean_array_uset(v_bs_x27_4165_, v_i_4159_, v___x_4166_);
v_i_4159_ = v___x_4168_;
v_bs_4160_ = v___x_4169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object* v___x_4171_, lean_object* v_sz_4172_, lean_object* v_i_4173_, lean_object* v_bs_4174_){
_start:
{
size_t v_sz_boxed_4175_; size_t v_i_boxed_4176_; lean_object* v_res_4177_; 
v_sz_boxed_4175_ = lean_unbox_usize(v_sz_4172_);
lean_dec(v_sz_4172_);
v_i_boxed_4176_ = lean_unbox_usize(v_i_4173_);
lean_dec(v_i_4173_);
v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4171_, v_sz_boxed_4175_, v_i_boxed_4176_, v_bs_4174_);
return v_res_4177_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCoinductive___closed__1(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = ((lean_object*)(l_Lean_Elab_Command_elabCoinductive___closed__0));
v___x_4180_ = l_Lean_stringToMessageData(v___x_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object* v_coinductiveElabData_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v_toCold_4189_; lean_object* v_options_4190_; lean_object* v_inheritedTraceOptions_4191_; uint8_t v_hasTrace_4192_; lean_object* v___x_4193_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; 
v_toCold_4189_ = lean_ctor_get(v_a_4186_, 0);
v_options_4190_ = lean_ctor_get(v_toCold_4189_, 2);
v_inheritedTraceOptions_4191_ = lean_ctor_get(v_toCold_4189_, 11);
v_hasTrace_4192_ = lean_ctor_get_uint8(v_options_4190_, sizeof(void*)*1);
v___x_4193_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4192_ == 0)
{
v___y_4195_ = v_a_4182_;
v___y_4196_ = v_a_4183_;
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
v___y_4199_ = v_a_4186_;
v___y_4200_ = v_a_4187_;
goto v___jp_4194_;
}
else
{
lean_object* v_cls_4262_; lean_object* v___x_4263_; uint8_t v___x_4264_; 
v_cls_4262_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4263_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4264_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4191_, v_options_4190_, v___x_4263_);
if (v___x_4264_ == 0)
{
v___y_4195_ = v_a_4182_;
v___y_4196_ = v_a_4183_;
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
v___y_4199_ = v_a_4186_;
v___y_4200_ = v_a_4187_;
goto v___jp_4194_;
}
else
{
lean_object* v___x_4265_; size_t v_sz_4266_; size_t v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4265_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4266_ = lean_array_size(v_coinductiveElabData_4181_);
v___x_4267_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4181_);
v___x_4268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4266_, v___x_4267_, v_coinductiveElabData_4181_);
v___x_4269_ = lean_array_to_list(v___x_4268_);
v___x_4270_ = lean_box(0);
v___x_4271_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4269_, v___x_4270_);
v___x_4272_ = l_Lean_MessageData_ofList(v___x_4271_);
v___x_4273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4273_, 0, v___x_4265_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4262_, v___x_4273_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_dec_ref_known(v___x_4274_, 1);
v___y_4195_ = v_a_4182_;
v___y_4196_ = v_a_4183_;
v___y_4197_ = v_a_4184_;
v___y_4198_ = v_a_4185_;
v___y_4199_ = v_a_4186_;
v___y_4200_ = v_a_4187_;
goto v___jp_4194_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4181_);
return v___x_4274_;
}
}
}
v___jp_4194_:
{
size_t v_sz_4201_; size_t v___x_4202_; lean_object* v___x_4203_; 
v_sz_4201_ = lean_array_size(v_coinductiveElabData_4181_);
v___x_4202_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4181_);
v___x_4203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4201_, v___x_4202_, v_coinductiveElabData_4181_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v_toConstantVal_4207_; lean_object* v_numParams_4208_; lean_object* v_levelParams_4209_; lean_object* v_type_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; size_t v_sz_4215_; lean_object* v___x_4216_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc_n(v_a_4204_, 2);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = lean_unsigned_to_nat(0u);
v___x_4206_ = lean_array_get_borrowed(v___x_4193_, v_a_4204_, v___x_4205_);
v_toConstantVal_4207_ = lean_ctor_get(v___x_4206_, 0);
v_numParams_4208_ = lean_ctor_get(v___x_4206_, 1);
v_levelParams_4209_ = lean_ctor_get(v_toConstantVal_4207_, 1);
v_type_4210_ = lean_ctor_get(v_toConstantVal_4207_, 2);
v___x_4211_ = lean_box(0);
lean_inc(v_levelParams_4209_);
v___x_4212_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4209_, v___x_4211_);
v___x_4213_ = lean_array_get_size(v_a_4204_);
v___x_4214_ = lean_nat_sub(v_numParams_4208_, v___x_4213_);
v_sz_4215_ = lean_array_size(v_a_4204_);
lean_inc(v___x_4214_);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4214_, v_sz_4215_, v___x_4202_, v_a_4204_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; size_t v_sz_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; lean_object* v___x_4225_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc_n(v_a_4217_, 2);
lean_dec_ref_known(v___x_4216_, 1);
v_sz_4218_ = lean_array_size(v_a_4217_);
lean_inc(v___x_4212_);
v___x_4219_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4212_, v_sz_4218_, v___x_4202_, v_a_4217_);
v___x_4220_ = lean_box_usize(v_sz_4215_);
v___x_4221_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4204_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4222_, 0, v___x_4212_);
lean_closure_set(v___f_4222_, 1, v___x_4219_);
lean_closure_set(v___f_4222_, 2, v___x_4220_);
lean_closure_set(v___f_4222_, 3, v___x_4221_);
lean_closure_set(v___f_4222_, 4, v_a_4204_);
lean_inc(v___x_4214_);
v___x_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4214_);
v___x_4224_ = 0;
lean_inc_ref(v_type_4210_);
v___x_4225_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4210_, v___x_4223_, v___f_4222_, v___x_4224_, v___x_4224_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; lean_object* v_env_4228_; size_t v_sz_4229_; lean_object* v_lctx_4230_; lean_object* v_localInstances_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = lean_st_ref_get(v___y_4200_);
v_env_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc_ref(v_env_4228_);
lean_dec(v___x_4227_);
v_sz_4229_ = lean_array_size(v_a_4226_);
v_lctx_4230_ = lean_ctor_get(v___y_4197_, 2);
v_localInstances_4231_ = lean_ctor_get(v___y_4197_, 3);
lean_inc(v_levelParams_4209_);
v___x_4232_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4181_, v_env_4228_, v_a_4217_, v_levelParams_4209_, v_sz_4229_, v___x_4202_, v_a_4226_);
lean_dec(v_a_4217_);
lean_inc_ref(v_localInstances_4231_);
lean_inc_ref(v_lctx_4230_);
v___x_4233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4233_, 0, v_lctx_4230_);
lean_ctor_set(v___x_4233_, 1, v_localInstances_4231_);
v___x_4234_ = l_Lean_Elab_partialFixpoint(v___x_4233_, v___x_4232_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_object* v___x_4235_; 
lean_dec_ref_known(v___x_4234_, 1);
lean_inc(v_a_4204_);
v___x_4235_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4204_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v___x_4236_; 
lean_dec_ref_known(v___x_4235_, 1);
lean_inc(v_a_4204_);
v___x_4236_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4214_, v_a_4204_, v_coinductiveElabData_4181_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v___x_4237_; 
lean_dec_ref_known(v___x_4236_, 1);
v___x_4237_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4204_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
return v___x_4237_;
}
else
{
lean_dec(v_a_4204_);
return v___x_4236_;
}
}
else
{
lean_dec(v___x_4214_);
lean_dec(v_a_4204_);
lean_dec_ref(v_coinductiveElabData_4181_);
return v___x_4235_;
}
}
else
{
lean_dec(v___x_4214_);
lean_dec(v_a_4204_);
lean_dec_ref(v_coinductiveElabData_4181_);
return v___x_4234_;
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec(v_a_4217_);
lean_dec(v___x_4214_);
lean_dec(v_a_4204_);
lean_dec_ref(v_coinductiveElabData_4181_);
v_a_4238_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4225_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4225_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
lean_dec(v___x_4214_);
lean_dec(v___x_4212_);
lean_dec(v_a_4204_);
lean_dec_ref(v_coinductiveElabData_4181_);
v_a_4246_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4216_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4216_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
return v___x_4251_;
}
}
}
}
else
{
lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4261_; 
lean_dec_ref(v_coinductiveElabData_4181_);
v_a_4254_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4261_ == 0)
{
v___x_4256_ = v___x_4203_;
v_isShared_4257_ = v_isSharedCheck_4261_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4203_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4284_, lean_object* v___x_4285_, lean_object* v_params_4286_, size_t v_sz_4287_, size_t v_i_4288_, lean_object* v_bs_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4284_, v___x_4285_, v_params_4286_, v_sz_4287_, v_i_4288_, v_bs_4289_, v___y_4292_, v___y_4293_, v___y_4294_, v___y_4295_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4298_, lean_object* v___x_4299_, lean_object* v_params_4300_, lean_object* v_sz_4301_, lean_object* v_i_4302_, lean_object* v_bs_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
size_t v_sz_boxed_4311_; size_t v_i_boxed_4312_; lean_object* v_res_4313_; 
v_sz_boxed_4311_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v_i_boxed_4312_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_res_4313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4298_, v___x_4299_, v_params_4300_, v_sz_boxed_4311_, v_i_boxed_4312_, v_bs_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4314_, lean_object* v___x_4315_, lean_object* v_a_4316_, lean_object* v___x_4317_, lean_object* v_as_4318_, size_t v_sz_4319_, size_t v_i_4320_, lean_object* v_bs_4321_){
_start:
{
lean_object* v___x_4322_; 
v___x_4322_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4314_, v___x_4315_, v_a_4316_, v___x_4317_, v_sz_4319_, v_i_4320_, v_bs_4321_);
return v___x_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4323_, lean_object* v___x_4324_, lean_object* v_a_4325_, lean_object* v___x_4326_, lean_object* v_as_4327_, lean_object* v_sz_4328_, lean_object* v_i_4329_, lean_object* v_bs_4330_){
_start:
{
size_t v_sz_boxed_4331_; size_t v_i_boxed_4332_; lean_object* v_res_4333_; 
v_sz_boxed_4331_ = lean_unbox_usize(v_sz_4328_);
lean_dec(v_sz_4328_);
v_i_boxed_4332_ = lean_unbox_usize(v_i_4329_);
lean_dec(v_i_4329_);
v_res_4333_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4323_, v___x_4324_, v_a_4325_, v___x_4326_, v_as_4327_, v_sz_boxed_4331_, v_i_boxed_4332_, v_bs_4330_);
lean_dec_ref(v_as_4327_);
lean_dec_ref(v_a_4325_);
lean_dec_ref(v_coinductiveElabData_4323_);
return v_res_4333_;
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
