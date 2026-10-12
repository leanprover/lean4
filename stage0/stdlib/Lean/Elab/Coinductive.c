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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__27;
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
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_70_;
v_res_70_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_();
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2____boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_();
return v_res_72_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1(void){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_75_ = lean_box(0);
v___x_76_ = 0;
v___x_77_ = ((lean_object*)(l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0));
v___x_78_ = l_Lean_Elab_instInhabitedModifiers_default;
v___x_79_ = lean_box(0);
v___x_80_ = lean_box(0);
v___x_81_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_80_);
lean_ctor_set(v___x_81_, 3, v___x_78_);
lean_ctor_set(v___x_81_, 4, v___x_77_);
lean_ctor_set(v___x_81_, 5, v___x_75_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*6, v___x_76_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1, &l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1_once, _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addFunctorPostfix(lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lean_Elab_Command_addFunctorPostfix___closed__1));
v___x_89_ = l_Lean_Name_append(v_x_87_, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfix(lean_object* v_x_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_Name_hasMacroScopes(v_x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Name_getPrefix(v_x_90_);
lean_dec(v_x_90_);
return v___x_92_;
}
else
{
lean_object* v_view_93_; lean_object* v_name_94_; lean_object* v_imported_95_; lean_object* v_ctx_96_; lean_object* v_scopes_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_106_; 
v_view_93_ = l_Lean_extractMacroScopes(v_x_90_);
v_name_94_ = lean_ctor_get(v_view_93_, 0);
v_imported_95_ = lean_ctor_get(v_view_93_, 1);
v_ctx_96_ = lean_ctor_get(v_view_93_, 2);
v_scopes_97_ = lean_ctor_get(v_view_93_, 3);
v_isSharedCheck_106_ = !lean_is_exclusive(v_view_93_);
if (v_isSharedCheck_106_ == 0)
{
v___x_99_ = v_view_93_;
v_isShared_100_ = v_isSharedCheck_106_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_scopes_97_);
lean_inc(v_ctx_96_);
lean_inc(v_imported_95_);
lean_inc(v_name_94_);
lean_dec(v_view_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_106_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_101_ = l_Lean_Name_getPrefix(v_name_94_);
lean_dec(v_name_94_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_101_);
v___x_103_ = v___x_99_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_101_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_imported_95_);
lean_ctor_set(v_reuseFailAlloc_105_, 2, v_ctx_96_);
lean_ctor_set(v_reuseFailAlloc_105_, 3, v_scopes_97_);
v___x_103_ = v_reuseFailAlloc_105_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_MacroScopesView_review(v___x_103_);
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(lean_object* v_msg_107_){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_box(0);
v___x_109_ = lean_panic_fn_borrowed(v___x_108_, v_msg_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_113_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2));
v___x_114_ = lean_unsigned_to_nat(13u);
v___x_115_ = lean_unsigned_to_nat(126u);
v___x_116_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1));
v___x_117_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0));
v___x_118_ = l_mkPanicMessageWithDecl(v___x_117_, v___x_116_, v___x_115_, v___x_114_, v___x_113_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor(lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_119_) == 1)
{
lean_object* v_pre_120_; lean_object* v_str_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_pre_120_ = lean_ctor_get(v_x_119_, 0);
lean_inc(v_pre_120_);
v_str_121_ = lean_ctor_get(v_x_119_, 1);
lean_inc_ref(v_str_121_);
lean_dec_ref_known(v_x_119_, 2);
v___x_122_ = l_Lean_Elab_Command_removeFunctorPostfix(v_pre_120_);
v___x_123_ = l_Lean_Name_str___override(v___x_122_, v_str_121_);
return v___x_123_;
}
else
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v_x_119_);
v___x_124_ = lean_obj_once(&l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3, &l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3_once, _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3);
v___x_125_ = l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(v___x_124_);
return v___x_125_;
}
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(lean_object* v_goal_131_, lean_object* v_eq_132_, uint8_t v_symm_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; 
lean_inc(v_goal_131_);
v___x_139_ = l_Lean_MVarId_getType(v_goal_131_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref_known(v___x_139_, 1);
v___x_141_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v_goal_131_);
v___x_142_ = l_Lean_MVarId_rewrite(v_goal_131_, v_a_140_, v_eq_132_, v_symm_133_, v___x_141_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v_eNew_144_; lean_object* v_eqProof_145_; lean_object* v___x_146_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_142_, 1);
v_eNew_144_ = lean_ctor_get(v_a_143_, 0);
lean_inc_ref(v_eNew_144_);
v_eqProof_145_ = lean_ctor_get(v_a_143_, 1);
lean_inc_ref(v_eqProof_145_);
lean_dec(v_a_143_);
v___x_146_ = l_Lean_MVarId_replaceTargetEq(v_goal_131_, v_eNew_144_, v_eqProof_145_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
return v___x_146_;
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec(v_goal_131_);
v_a_147_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_142_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_142_);
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
else
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
lean_dec_ref(v_eq_132_);
lean_dec(v_goal_131_);
v_a_155_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_139_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_139_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_goal_131_ = stack[0].m_obj;
lean_object* v_eq_132_ = stack[1].m_obj;
uint8_t v_symm_133_ = stack[2].m_num;
lean_object* v_a_134_ = stack[3].m_obj;
lean_object* v_a_135_ = stack[4].m_obj;
lean_object* v_a_136_ = stack[5].m_obj;
lean_object* v_a_137_ = stack[6].m_obj;
lean_object* v_res_163_;
v_res_163_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v_goal_131_, v_eq_132_, v_symm_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___boxed(lean_object* v_goal_164_, lean_object* v_eq_165_, lean_object* v_symm_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
uint8_t v_symm_boxed_172_; lean_object* v_res_173_; 
v_symm_boxed_172_ = lean_unbox(v_symm_166_);
v_res_173_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v_goal_164_, v_eq_165_, v_symm_boxed_172_, v_a_167_, v_a_168_, v_a_169_, v_a_170_);
lean_dec(v_a_170_);
lean_dec_ref(v_a_169_);
lean_dec(v_a_168_);
lean_dec_ref(v_a_167_);
return v_res_173_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(lean_object* v_e_174_, lean_object* v___y_175_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Lean_Expr_hasMVar(v_e_174_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v_e_174_);
return v___x_178_;
}
else
{
lean_object* v___x_179_; lean_object* v_mctx_180_; lean_object* v___x_181_; lean_object* v_fst_182_; lean_object* v_snd_183_; lean_object* v___x_184_; lean_object* v_cache_185_; lean_object* v_zetaDeltaFVarIds_186_; lean_object* v_postponed_187_; lean_object* v_diag_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_197_; 
v___x_179_ = lean_st_ref_get(v___y_175_);
v_mctx_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc_ref(v_mctx_180_);
lean_dec(v___x_179_);
v___x_181_ = l_Lean_instantiateMVarsCore(v_mctx_180_, v_e_174_);
v_fst_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_fst_182_);
v_snd_183_ = lean_ctor_get(v___x_181_, 1);
lean_inc(v_snd_183_);
lean_dec_ref(v___x_181_);
v___x_184_ = lean_st_ref_take(v___y_175_);
v_cache_185_ = lean_ctor_get(v___x_184_, 1);
v_zetaDeltaFVarIds_186_ = lean_ctor_get(v___x_184_, 2);
v_postponed_187_ = lean_ctor_get(v___x_184_, 3);
v_diag_188_ = lean_ctor_get(v___x_184_, 4);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_197_ == 0)
{
lean_object* v_unused_198_; 
v_unused_198_ = lean_ctor_get(v___x_184_, 0);
lean_dec(v_unused_198_);
v___x_190_ = v___x_184_;
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_diag_188_);
lean_inc(v_postponed_187_);
lean_inc(v_zetaDeltaFVarIds_186_);
lean_inc(v_cache_185_);
lean_dec(v___x_184_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_197_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 0, v_snd_183_);
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_snd_183_);
lean_ctor_set(v_reuseFailAlloc_196_, 1, v_cache_185_);
lean_ctor_set(v_reuseFailAlloc_196_, 2, v_zetaDeltaFVarIds_186_);
lean_ctor_set(v_reuseFailAlloc_196_, 3, v_postponed_187_);
lean_ctor_set(v_reuseFailAlloc_196_, 4, v_diag_188_);
v___x_193_ = v_reuseFailAlloc_196_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_st_ref_put(v___y_175_, v___x_193_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_fst_182_);
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_174_ = stack[0].m_obj;
lean_object* v___y_175_ = stack[1].m_obj;
lean_object* v_res_199_;
v_res_199_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_174_, v___y_175_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg___boxed(lean_object* v_e_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_200_, v___y_201_);
lean_dec(v___y_201_);
return v_res_203_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(lean_object* v_e_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_204_, v___y_206_);
return v___x_210_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_204_ = stack[0].m_obj;
lean_object* v___y_205_ = stack[1].m_obj;
lean_object* v___y_206_ = stack[2].m_obj;
lean_object* v___y_207_ = stack[3].m_obj;
lean_object* v___y_208_ = stack[4].m_obj;
lean_object* v_res_211_;
v_res_211_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(v_e_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
stack->m_obj
 = v_res_211_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___boxed(lean_object* v_e_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(v_e_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_218_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(lean_object* v_k_219_, lean_object* v_b_220_, lean_object* v_c_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; 
lean_inc(v___y_225_);
lean_inc_ref(v___y_224_);
lean_inc(v___y_223_);
lean_inc_ref(v___y_222_);
v___x_227_ = lean_apply_7(v_k_219_, v_b_220_, v_c_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, lean_box(0));
return v___x_227_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_219_ = stack[0].m_obj;
lean_object* v_b_220_ = stack[1].m_obj;
lean_object* v_c_221_ = stack[2].m_obj;
lean_object* v___y_222_ = stack[3].m_obj;
lean_object* v___y_223_ = stack[4].m_obj;
lean_object* v___y_224_ = stack[5].m_obj;
lean_object* v___y_225_ = stack[6].m_obj;
lean_object* v_res_228_;
v_res_228_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(v_k_219_, v_b_220_, v_c_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed(lean_object* v_k_229_, lean_object* v_b_230_, lean_object* v_c_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(v_k_229_, v_b_230_, v_c_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
return v_res_237_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(lean_object* v_type_238_, lean_object* v_k_239_, uint8_t v_cleanupAnnotations_240_, uint8_t v_whnfType_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; 
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_247_, 0, v_k_239_);
v___x_248_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_238_, v___f_247_, v_cleanupAnnotations_240_, v_whnfType_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_248_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_248_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_238_ = stack[0].m_obj;
lean_object* v_k_239_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_240_ = stack[2].m_num;
uint8_t v_whnfType_241_ = stack[3].m_num;
lean_object* v___y_242_ = stack[4].m_obj;
lean_object* v___y_243_ = stack[5].m_obj;
lean_object* v___y_244_ = stack[6].m_obj;
lean_object* v___y_245_ = stack[7].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_238_, v_k_239_, v_cleanupAnnotations_240_, v_whnfType_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___boxed(lean_object* v_type_266_, lean_object* v_k_267_, lean_object* v_cleanupAnnotations_268_, lean_object* v_whnfType_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_275_; uint8_t v_whnfType_boxed_276_; lean_object* v_res_277_; 
v_cleanupAnnotations_boxed_275_ = lean_unbox(v_cleanupAnnotations_268_);
v_whnfType_boxed_276_ = lean_unbox(v_whnfType_269_);
v_res_277_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_266_, v_k_267_, v_cleanupAnnotations_boxed_275_, v_whnfType_boxed_276_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_277_;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(lean_object* v_00_u03b1_278_, lean_object* v_type_279_, lean_object* v_k_280_, uint8_t v_cleanupAnnotations_281_, uint8_t v_whnfType_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_279_, v_k_280_, v_cleanupAnnotations_281_, v_whnfType_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
return v___x_288_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_279_ = stack[1].m_obj;
lean_object* v_k_280_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_281_ = stack[3].m_num;
uint8_t v_whnfType_282_ = stack[4].m_num;
lean_object* v___y_283_ = stack[5].m_obj;
lean_object* v___y_284_ = stack[6].m_obj;
lean_object* v___y_285_ = stack[7].m_obj;
lean_object* v___y_286_ = stack[8].m_obj;
lean_object* v_res_289_;
v_res_289_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(lean_box(0), v_type_279_, v_k_280_, v_cleanupAnnotations_281_, v_whnfType_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___boxed(lean_object* v_00_u03b1_290_, lean_object* v_type_291_, lean_object* v_k_292_, lean_object* v_cleanupAnnotations_293_, lean_object* v_whnfType_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_300_; uint8_t v_whnfType_boxed_301_; lean_object* v_res_302_; 
v_cleanupAnnotations_boxed_300_ = lean_unbox(v_cleanupAnnotations_293_);
v_whnfType_boxed_301_ = lean_unbox(v_whnfType_294_);
v_res_302_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(v_00_u03b1_290_, v_type_291_, v_k_292_, v_cleanupAnnotations_boxed_300_, v_whnfType_boxed_301_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_302_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(lean_object* v_name_303_, lean_object* v_levelParams_304_, lean_object* v_type_305_, lean_object* v_value_306_, lean_object* v_hints_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; uint8_t v___y_312_; uint8_t v___y_319_; lean_object* v_env_322_; uint8_t v___x_323_; 
v___x_310_ = lean_st_ref_get(v___y_308_);
v_env_322_ = lean_ctor_get(v___x_310_, 0);
lean_inc_ref_n(v_env_322_, 2);
lean_dec(v___x_310_);
v___x_323_ = l_Lean_Environment_hasUnsafe(v_env_322_, v_type_305_);
if (v___x_323_ == 0)
{
uint8_t v___x_324_; 
v___x_324_ = l_Lean_Environment_hasUnsafe(v_env_322_, v_value_306_);
v___y_319_ = v___x_324_;
goto v___jp_318_;
}
else
{
lean_dec_ref(v_env_322_);
v___y_319_ = v___x_323_;
goto v___jp_318_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_inc(v_name_303_);
v___x_313_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_313_, 0, v_name_303_);
lean_ctor_set(v___x_313_, 1, v_levelParams_304_);
lean_ctor_set(v___x_313_, 2, v_type_305_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v_name_303_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_316_, 0, v___x_313_);
lean_ctor_set(v___x_316_, 1, v_value_306_);
lean_ctor_set(v___x_316_, 2, v_hints_307_);
lean_ctor_set(v___x_316_, 3, v___x_315_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*4, v___y_312_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
v___jp_318_:
{
if (v___y_319_ == 0)
{
uint8_t v___x_320_; 
v___x_320_ = 1;
v___y_312_ = v___x_320_;
goto v___jp_311_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = 0;
v___y_312_ = v___x_321_;
goto v___jp_311_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_303_ = stack[0].m_obj;
lean_object* v_levelParams_304_ = stack[1].m_obj;
lean_object* v_type_305_ = stack[2].m_obj;
lean_object* v_value_306_ = stack[3].m_obj;
lean_object* v_hints_307_ = stack[4].m_obj;
lean_object* v___y_308_ = stack[5].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_303_, v_levelParams_304_, v_type_305_, v_value_306_, v_hints_307_, v___y_308_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg___boxed(lean_object* v_name_326_, lean_object* v_levelParams_327_, lean_object* v_type_328_, lean_object* v_value_329_, lean_object* v_hints_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_326_, v_levelParams_327_, v_type_328_, v_value_329_, v_hints_330_, v___y_331_);
lean_dec(v___y_331_);
return v_res_333_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(lean_object* v_name_334_, lean_object* v_levelParams_335_, lean_object* v_type_336_, lean_object* v_value_337_, lean_object* v_hints_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v_name_334_, v_levelParams_335_, v_type_336_, v_value_337_, v_hints_338_, v___y_342_);
return v___x_344_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_334_ = stack[0].m_obj;
lean_object* v_levelParams_335_ = stack[1].m_obj;
lean_object* v_type_336_ = stack[2].m_obj;
lean_object* v_value_337_ = stack[3].m_obj;
lean_object* v_hints_338_ = stack[4].m_obj;
lean_object* v___y_339_ = stack[5].m_obj;
lean_object* v___y_340_ = stack[6].m_obj;
lean_object* v___y_341_ = stack[7].m_obj;
lean_object* v___y_342_ = stack[8].m_obj;
lean_object* v_res_345_;
v_res_345_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(v_name_334_, v_levelParams_335_, v_type_336_, v_value_337_, v_hints_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
stack->m_obj
 = v_res_345_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___boxed(lean_object* v_name_346_, lean_object* v_levelParams_347_, lean_object* v_type_348_, lean_object* v_value_349_, lean_object* v_hints_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7(v_name_346_, v_levelParams_347_, v_type_348_, v_value_349_, v_hints_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
if (lean_obj_tag(v_a_357_) == 0)
{
lean_object* v___x_359_; 
v___x_359_ = l_List_reverse___redArg(v_a_358_);
return v___x_359_;
}
else
{
lean_object* v_head_360_; lean_object* v_tail_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_370_; 
v_head_360_ = lean_ctor_get(v_a_357_, 0);
v_tail_361_ = lean_ctor_get(v_a_357_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_a_357_);
if (v_isSharedCheck_370_ == 0)
{
v___x_363_ = v_a_357_;
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_tail_361_);
lean_inc(v_head_360_);
lean_dec(v_a_357_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_370_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = l_Lean_mkLevelParam(v_head_360_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v_a_358_);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v_a_358_);
v___x_367_ = v_reuseFailAlloc_369_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
v_a_357_ = v_tail_361_;
v_a_358_ = v___x_367_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_ks_375_; lean_object* v_vs_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_400_; 
v_ks_375_ = lean_ctor_get(v_x_371_, 0);
v_vs_376_ = lean_ctor_get(v_x_371_, 1);
v_isSharedCheck_400_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_400_ == 0)
{
v___x_378_ = v_x_371_;
v_isShared_379_ = v_isSharedCheck_400_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_vs_376_);
lean_inc(v_ks_375_);
lean_dec(v_x_371_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_400_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
v___x_380_ = lean_array_get_size(v_ks_375_);
v___x_381_ = lean_nat_dec_lt(v_x_372_, v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec(v_x_372_);
v___x_382_ = lean_array_push(v_ks_375_, v_x_373_);
v___x_383_ = lean_array_push(v_vs_376_, v_x_374_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_383_);
lean_ctor_set(v___x_378_, 0, v___x_382_);
v___x_385_ = v___x_378_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_382_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
else
{
lean_object* v_k_x27_387_; uint8_t v___x_388_; 
v_k_x27_387_ = lean_array_fget_borrowed(v_ks_375_, v_x_372_);
v___x_388_ = l_Lean_instBEqMVarId_beq(v_x_373_, v_k_x27_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_390_; 
if (v_isShared_379_ == 0)
{
v___x_390_ = v___x_378_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_ks_375_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_vs_376_);
v___x_390_ = v_reuseFailAlloc_394_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_nat_add(v_x_372_, v___x_391_);
lean_dec(v_x_372_);
v_x_371_ = v___x_390_;
v_x_372_ = v___x_392_;
goto _start;
}
}
else
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_395_ = lean_array_fset(v_ks_375_, v_x_372_, v_x_373_);
v___x_396_ = lean_array_fset(v_vs_376_, v_x_372_, v_x_374_);
lean_dec(v_x_372_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 1, v___x_396_);
lean_ctor_set(v___x_378_, 0, v___x_395_);
v___x_398_ = v___x_378_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_395_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(lean_object* v_n_401_, lean_object* v_k_402_, lean_object* v_v_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_n_401_, v___x_404_, v_k_402_, v_v_403_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_406_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(lean_object* v_x_407_, size_t v_x_408_, size_t v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
if (lean_obj_tag(v_x_407_) == 0)
{
lean_object* v_es_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v_j_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_es_412_ = lean_ctor_get(v_x_407_, 0);
v___x_413_ = ((size_t)31ULL);
v___x_414_ = lean_usize_land(v_x_408_, v___x_413_);
v_j_415_ = lean_usize_to_nat(v___x_414_);
v___x_416_ = lean_array_get_size(v_es_412_);
v___x_417_ = lean_nat_dec_lt(v_j_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_dec(v_j_415_);
lean_dec(v_x_411_);
lean_dec(v_x_410_);
return v_x_407_;
}
else
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_456_; 
lean_inc_ref(v_es_412_);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v_x_407_, 0);
lean_dec(v_unused_457_);
v___x_419_ = v_x_407_;
v_isShared_420_ = v_isSharedCheck_456_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_x_407_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_456_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_v_421_; lean_object* v___x_422_; lean_object* v_xs_x27_423_; lean_object* v___y_425_; 
v_v_421_ = lean_array_fget(v_es_412_, v_j_415_);
v___x_422_ = lean_box(0);
v_xs_x27_423_ = lean_array_fset(v_es_412_, v_j_415_, v___x_422_);
switch(lean_obj_tag(v_v_421_))
{
case 0:
{
lean_object* v_key_430_; lean_object* v_val_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_441_; 
v_key_430_ = lean_ctor_get(v_v_421_, 0);
v_val_431_ = lean_ctor_get(v_v_421_, 1);
v_isSharedCheck_441_ = !lean_is_exclusive(v_v_421_);
if (v_isSharedCheck_441_ == 0)
{
v___x_433_ = v_v_421_;
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_val_431_);
lean_inc(v_key_430_);
lean_dec(v_v_421_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_441_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
uint8_t v___x_435_; 
v___x_435_ = l_Lean_instBEqMVarId_beq(v_x_410_, v_key_430_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; lean_object* v___x_437_; 
lean_del_object(v___x_433_);
v___x_436_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_430_, v_val_431_, v_x_410_, v_x_411_);
v___x_437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_437_, 0, v___x_436_);
v___y_425_ = v___x_437_;
goto v___jp_424_;
}
else
{
lean_object* v___x_439_; 
lean_dec(v_val_431_);
lean_dec(v_key_430_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v_x_411_);
lean_ctor_set(v___x_433_, 0, v_x_410_);
v___x_439_ = v___x_433_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_x_410_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_x_411_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
v___y_425_ = v___x_439_;
goto v___jp_424_;
}
}
}
}
case 1:
{
lean_object* v_node_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_454_; 
v_node_442_ = lean_ctor_get(v_v_421_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v_v_421_);
if (v_isSharedCheck_454_ == 0)
{
v___x_444_ = v_v_421_;
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_node_442_);
lean_dec(v_v_421_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_454_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
size_t v___x_446_; size_t v___x_447_; size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_446_ = ((size_t)5ULL);
v___x_447_ = lean_usize_shift_right(v_x_408_, v___x_446_);
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_x_409_, v___x_448_);
v___x_450_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_node_442_, v___x_447_, v___x_449_, v_x_410_, v_x_411_);
if (v_isShared_445_ == 0)
{
lean_ctor_set(v___x_444_, 0, v___x_450_);
v___x_452_ = v___x_444_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
v___y_425_ = v___x_452_;
goto v___jp_424_;
}
}
}
default: 
{
lean_object* v___x_455_; 
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v_x_410_);
lean_ctor_set(v___x_455_, 1, v_x_411_);
v___y_425_ = v___x_455_;
goto v___jp_424_;
}
}
v___jp_424_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_array_fset(v_xs_x27_423_, v_j_415_, v___y_425_);
lean_dec(v_j_415_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 0, v___x_426_);
v___x_428_ = v___x_419_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
else
{
lean_object* v_ks_458_; lean_object* v_vs_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_477_; 
v_ks_458_ = lean_ctor_get(v_x_407_, 0);
v_vs_459_ = lean_ctor_get(v_x_407_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_407_);
if (v_isSharedCheck_477_ == 0)
{
v___x_461_ = v_x_407_;
v_isShared_462_ = v_isSharedCheck_477_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_vs_459_);
lean_inc(v_ks_458_);
lean_dec(v_x_407_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_477_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_464_; 
if (v_isShared_462_ == 0)
{
v___x_464_ = v___x_461_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_ks_458_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_vs_459_);
v___x_464_ = v_reuseFailAlloc_476_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v_newNode_465_; size_t v___x_466_; uint8_t v___x_467_; 
v_newNode_465_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v___x_464_, v_x_410_, v_x_411_);
v___x_466_ = ((size_t)7ULL);
v___x_467_ = lean_usize_dec_le(v___x_466_, v_x_409_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_468_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_465_);
v___x_469_ = lean_unsigned_to_nat(4u);
v___x_470_ = lean_nat_dec_lt(v___x_468_, v___x_469_);
lean_dec(v___x_468_);
if (v___x_470_ == 0)
{
lean_object* v_ks_471_; lean_object* v_vs_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v_ks_471_ = lean_ctor_get(v_newNode_465_, 0);
lean_inc_ref(v_ks_471_);
v_vs_472_ = lean_ctor_get(v_newNode_465_, 1);
lean_inc_ref(v_vs_472_);
lean_dec_ref(v_newNode_465_);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0);
v___x_475_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_x_409_, v_ks_471_, v_vs_472_, v___x_473_, v___x_474_);
lean_dec_ref(v_vs_472_);
lean_dec_ref(v_ks_471_);
return v___x_475_;
}
else
{
return v_newNode_465_;
}
}
else
{
return v_newNode_465_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_407_ = stack[0].m_obj;
size_t v_x_408_ = stack[1].m_num;
size_t v_x_409_ = stack[2].m_num;
lean_object* v_x_410_ = stack[3].m_obj;
lean_object* v_x_411_ = stack[4].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_407_, v_x_408_, v_x_409_, v_x_410_, v_x_411_);
stack->m_obj
 = v_res_478_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(size_t v_depth_479_, lean_object* v_keys_480_, lean_object* v_vals_481_, lean_object* v_i_482_, lean_object* v_entries_483_){
_start:
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_array_get_size(v_keys_480_);
v___x_485_ = lean_nat_dec_lt(v_i_482_, v___x_484_);
if (v___x_485_ == 0)
{
lean_dec(v_i_482_);
return v_entries_483_;
}
else
{
lean_object* v_k_486_; lean_object* v_v_487_; uint64_t v___x_488_; size_t v_h_489_; size_t v___x_490_; lean_object* v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v_h_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v_k_486_ = lean_array_fget_borrowed(v_keys_480_, v_i_482_);
v_v_487_ = lean_array_fget_borrowed(v_vals_481_, v_i_482_);
v___x_488_ = l_Lean_instHashableMVarId_hash(v_k_486_);
v_h_489_ = lean_uint64_to_usize(v___x_488_);
v___x_490_ = ((size_t)5ULL);
v___x_491_ = lean_unsigned_to_nat(1u);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_sub(v_depth_479_, v___x_492_);
v___x_494_ = lean_usize_mul(v___x_490_, v___x_493_);
v_h_495_ = lean_usize_shift_right(v_h_489_, v___x_494_);
v___x_496_ = lean_nat_add(v_i_482_, v___x_491_);
lean_dec(v_i_482_);
lean_inc(v_v_487_);
lean_inc(v_k_486_);
v___x_497_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_entries_483_, v_h_495_, v_depth_479_, v_k_486_, v_v_487_);
v_i_482_ = v___x_496_;
v_entries_483_ = v___x_497_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_479_ = stack[0].m_num;
lean_object* v_keys_480_ = stack[1].m_obj;
lean_object* v_vals_481_ = stack[2].m_obj;
lean_object* v_i_482_ = stack[3].m_obj;
lean_object* v_entries_483_ = stack[4].m_obj;
lean_object* v_res_499_;
v_res_499_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_479_, v_keys_480_, v_vals_481_, v_i_482_, v_entries_483_);
stack->m_obj
 = v_res_499_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_depth_500_, lean_object* v_keys_501_, lean_object* v_vals_502_, lean_object* v_i_503_, lean_object* v_entries_504_){
_start:
{
size_t v_depth_boxed_505_; lean_object* v_res_506_; 
v_depth_boxed_505_ = lean_unbox_usize(v_depth_500_);
lean_dec(v_depth_500_);
v_res_506_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_boxed_505_, v_keys_501_, v_vals_502_, v_i_503_, v_entries_504_);
lean_dec_ref(v_vals_502_);
lean_dec_ref(v_keys_501_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
size_t v_x_8999__boxed_512_; size_t v_x_9000__boxed_513_; lean_object* v_res_514_; 
v_x_8999__boxed_512_ = lean_unbox_usize(v_x_508_);
lean_dec(v_x_508_);
v_x_9000__boxed_513_ = lean_unbox_usize(v_x_509_);
lean_dec(v_x_509_);
v_res_514_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_507_, v_x_8999__boxed_512_, v_x_9000__boxed_513_, v_x_510_, v_x_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_){
_start:
{
uint64_t v___x_518_; size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_518_ = l_Lean_instHashableMVarId_hash(v_x_516_);
v___x_519_ = lean_uint64_to_usize(v___x_518_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_515_, v___x_519_, v___x_520_, v_x_516_, v_x_517_);
return v___x_521_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object* v_mvarId_522_, lean_object* v_val_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; lean_object* v_mctx_527_; lean_object* v_cache_528_; lean_object* v_zetaDeltaFVarIds_529_; lean_object* v_postponed_530_; lean_object* v_diag_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_561_; 
v___x_526_ = lean_st_ref_take(v___y_524_);
v_mctx_527_ = lean_ctor_get(v___x_526_, 0);
v_cache_528_ = lean_ctor_get(v___x_526_, 1);
v_zetaDeltaFVarIds_529_ = lean_ctor_get(v___x_526_, 2);
v_postponed_530_ = lean_ctor_get(v___x_526_, 3);
v_diag_531_ = lean_ctor_get(v___x_526_, 4);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_561_ == 0)
{
v___x_533_ = v___x_526_;
v_isShared_534_ = v_isSharedCheck_561_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_diag_531_);
lean_inc(v_postponed_530_);
lean_inc(v_zetaDeltaFVarIds_529_);
lean_inc(v_cache_528_);
lean_inc(v_mctx_527_);
lean_dec(v___x_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_561_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_depth_535_; lean_object* v_levelAssignDepth_536_; lean_object* v_lmvarCounter_537_; lean_object* v_mvarCounter_538_; lean_object* v_lDecls_539_; lean_object* v_decls_540_; lean_object* v_userNames_541_; lean_object* v_lAssignment_542_; lean_object* v_eAssignment_543_; lean_object* v_dAssignment_544_; lean_object* v_instanceTypedMVars_545_; lean_object* v_synthNormMemo_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_560_; 
v_depth_535_ = lean_ctor_get(v_mctx_527_, 0);
v_levelAssignDepth_536_ = lean_ctor_get(v_mctx_527_, 1);
v_lmvarCounter_537_ = lean_ctor_get(v_mctx_527_, 2);
v_mvarCounter_538_ = lean_ctor_get(v_mctx_527_, 3);
v_lDecls_539_ = lean_ctor_get(v_mctx_527_, 4);
v_decls_540_ = lean_ctor_get(v_mctx_527_, 5);
v_userNames_541_ = lean_ctor_get(v_mctx_527_, 6);
v_lAssignment_542_ = lean_ctor_get(v_mctx_527_, 7);
v_eAssignment_543_ = lean_ctor_get(v_mctx_527_, 8);
v_dAssignment_544_ = lean_ctor_get(v_mctx_527_, 9);
v_instanceTypedMVars_545_ = lean_ctor_get(v_mctx_527_, 10);
v_synthNormMemo_546_ = lean_ctor_get(v_mctx_527_, 11);
v_isSharedCheck_560_ = !lean_is_exclusive(v_mctx_527_);
if (v_isSharedCheck_560_ == 0)
{
v___x_548_ = v_mctx_527_;
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_synthNormMemo_546_);
lean_inc(v_instanceTypedMVars_545_);
lean_inc(v_dAssignment_544_);
lean_inc(v_eAssignment_543_);
lean_inc(v_lAssignment_542_);
lean_inc(v_userNames_541_);
lean_inc(v_decls_540_);
lean_inc(v_lDecls_539_);
lean_inc(v_mvarCounter_538_);
lean_inc(v_lmvarCounter_537_);
lean_inc(v_levelAssignDepth_536_);
lean_inc(v_depth_535_);
lean_dec(v_mctx_527_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_560_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_550_ = lean_box(0);
v___x_551_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_543_, v_mvarId_522_, v_val_523_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 8, v___x_551_);
v___x_553_ = v___x_548_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_depth_535_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_levelAssignDepth_536_);
lean_ctor_set(v_reuseFailAlloc_559_, 2, v_lmvarCounter_537_);
lean_ctor_set(v_reuseFailAlloc_559_, 3, v_mvarCounter_538_);
lean_ctor_set(v_reuseFailAlloc_559_, 4, v_lDecls_539_);
lean_ctor_set(v_reuseFailAlloc_559_, 5, v_decls_540_);
lean_ctor_set(v_reuseFailAlloc_559_, 6, v_userNames_541_);
lean_ctor_set(v_reuseFailAlloc_559_, 7, v_lAssignment_542_);
lean_ctor_set(v_reuseFailAlloc_559_, 8, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_559_, 9, v_dAssignment_544_);
lean_ctor_set(v_reuseFailAlloc_559_, 10, v_instanceTypedMVars_545_);
lean_ctor_set(v_reuseFailAlloc_559_, 11, v_synthNormMemo_546_);
v___x_553_ = v_reuseFailAlloc_559_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_555_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_553_);
v___x_555_ = v___x_533_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_cache_528_);
lean_ctor_set(v_reuseFailAlloc_558_, 2, v_zetaDeltaFVarIds_529_);
lean_ctor_set(v_reuseFailAlloc_558_, 3, v_postponed_530_);
lean_ctor_set(v_reuseFailAlloc_558_, 4, v_diag_531_);
v___x_555_ = v_reuseFailAlloc_558_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_st_ref_put(v___y_524_, v___x_555_);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_550_);
return v___x_557_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_522_ = stack[0].m_obj;
lean_object* v_val_523_ = stack[1].m_obj;
lean_object* v___y_524_ = stack[2].m_obj;
lean_object* v_res_562_;
v_res_562_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_522_, v_val_523_, v___y_524_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object* v_mvarId_563_, lean_object* v_val_564_, lean_object* v___y_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_563_, v_val_564_, v___y_565_);
lean_dec(v___y_565_);
return v_res_567_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object* v_msgData_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_env_575_; uint8_t v___x_576_; lean_object* v_env_577_; lean_object* v___x_578_; lean_object* v_toCold_579_; lean_object* v_mctx_580_; lean_object* v_lctx_581_; lean_object* v_options_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_574_ = lean_st_ref_get(v___y_572_);
v_env_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_env_575_);
lean_dec(v___x_574_);
v___x_576_ = 0;
v_env_577_ = l_Lean_Environment_setRecordingDeps(v_env_575_, v___x_576_);
v___x_578_ = lean_st_ref_get(v___y_570_);
v_toCold_579_ = lean_ctor_get(v___y_571_, 0);
v_mctx_580_ = lean_ctor_get(v___x_578_, 0);
lean_inc_ref(v_mctx_580_);
lean_dec(v___x_578_);
v_lctx_581_ = lean_ctor_get(v___y_569_, 2);
v_options_582_ = lean_ctor_get(v_toCold_579_, 2);
lean_inc_ref(v_options_582_);
lean_inc_ref(v_lctx_581_);
v___x_583_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_583_, 0, v_env_577_);
lean_ctor_set(v___x_583_, 1, v_mctx_580_);
lean_ctor_set(v___x_583_, 2, v_lctx_581_);
lean_ctor_set(v___x_583_, 3, v_options_582_);
v___x_584_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
lean_ctor_set(v___x_584_, 1, v_msgData_568_);
v___x_585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_585_, 0, v___x_584_);
return v___x_585_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_568_ = stack[0].m_obj;
lean_object* v___y_569_ = stack[1].m_obj;
lean_object* v___y_570_ = stack[2].m_obj;
lean_object* v___y_571_ = stack[3].m_obj;
lean_object* v___y_572_ = stack[4].m_obj;
lean_object* v_res_586_;
v_res_586_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
stack->m_obj
 = v_res_586_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
return v_res_593_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_ref_600_; lean_object* v___x_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_610_; 
v_ref_600_ = lean_ctor_get(v___y_597_, 2);
v___x_601_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_610_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_610_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_608_; 
lean_inc(v_ref_600_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_ref_600_);
lean_ctor_set(v___x_606_, 1, v_a_602_);
if (v_isShared_605_ == 0)
{
lean_ctor_set_tag(v___x_604_, 1);
lean_ctor_set(v___x_604_, 0, v___x_606_);
v___x_608_ = v___x_604_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_594_ = stack[0].m_obj;
lean_object* v___y_595_ = stack[1].m_obj;
lean_object* v___y_596_ = stack[2].m_obj;
lean_object* v___y_597_ = stack[3].m_obj;
lean_object* v___y_598_ = stack[4].m_obj;
lean_object* v_res_611_;
v_res_611_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
return v_res_618_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_619_, lean_object* v_b_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_array_626_; lean_object* v_start_627_; lean_object* v_stop_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_643_; 
v_array_626_ = lean_ctor_get(v_a_619_, 0);
v_start_627_ = lean_ctor_get(v_a_619_, 1);
v_stop_628_ = lean_ctor_get(v_a_619_, 2);
v_isSharedCheck_643_ = !lean_is_exclusive(v_a_619_);
if (v_isSharedCheck_643_ == 0)
{
v___x_630_ = v_a_619_;
v_isShared_631_ = v_isSharedCheck_643_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_stop_628_);
lean_inc(v_start_627_);
lean_inc(v_array_626_);
lean_dec(v_a_619_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_643_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
uint8_t v___x_632_; 
v___x_632_ = lean_nat_dec_lt(v_start_627_, v_stop_628_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_del_object(v___x_630_);
lean_dec(v_stop_628_);
lean_dec(v_start_627_);
lean_dec_ref(v_array_626_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_b_620_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_start_627_, v___x_634_);
lean_inc_ref(v_array_626_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 1, v___x_635_);
v___x_637_ = v___x_630_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_array_626_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_stop_628_);
v___x_637_ = v_reuseFailAlloc_642_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = lean_array_fget(v_array_626_, v_start_627_);
lean_dec(v_start_627_);
lean_dec_ref(v_array_626_);
v___x_639_ = l_Lean_Meta_mkCongrFun(v_b_620_, v___x_638_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v_a_619_ = v___x_637_;
v_b_620_ = v_a_640_;
goto _start;
}
else
{
lean_dec_ref(v___x_637_);
return v___x_639_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_619_ = stack[0].m_obj;
lean_object* v_b_620_ = stack[1].m_obj;
lean_object* v___y_621_ = stack[2].m_obj;
lean_object* v___y_622_ = stack[3].m_obj;
lean_object* v___y_623_ = stack[4].m_obj;
lean_object* v___y_624_ = stack[5].m_obj;
lean_object* v_res_644_;
v_res_644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_619_, v_b_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_);
stack->m_obj
 = v_res_644_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_645_, lean_object* v_b_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_645_, v_b_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_652_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_653_, lean_object* v___x_654_, size_t v_sz_655_, size_t v_i_656_, lean_object* v_bs_657_){
_start:
{
uint8_t v___x_658_; 
v___x_658_ = lean_usize_dec_lt(v_i_656_, v_sz_655_);
if (v___x_658_ == 0)
{
lean_dec(v_levels_653_);
return v_bs_657_;
}
else
{
lean_object* v_v_659_; lean_object* v_toConstantVal_660_; lean_object* v_name_661_; lean_object* v___x_662_; lean_object* v_bs_x27_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
v_v_659_ = lean_array_uget_borrowed(v_bs_657_, v_i_656_);
v_toConstantVal_660_ = lean_ctor_get(v_v_659_, 0);
v_name_661_ = lean_ctor_get(v_toConstantVal_660_, 0);
lean_inc(v_name_661_);
v___x_662_ = lean_unsigned_to_nat(0u);
v_bs_x27_663_ = lean_array_uset(v_bs_657_, v_i_656_, v___x_662_);
v___x_664_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_661_);
lean_inc(v_levels_653_);
v___x_665_ = l_Lean_mkConst(v___x_664_, v_levels_653_);
v___x_666_ = l_Lean_mkAppN(v___x_665_, v___x_654_);
v___x_667_ = ((size_t)1ULL);
v___x_668_ = lean_usize_add(v_i_656_, v___x_667_);
v___x_669_ = lean_array_uset(v_bs_x27_663_, v_i_656_, v___x_666_);
v_i_656_ = v___x_668_;
v_bs_657_ = v___x_669_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_levels_653_ = stack[0].m_obj;
lean_object* v___x_654_ = stack[1].m_obj;
size_t v_sz_655_ = stack[2].m_num;
size_t v_i_656_ = stack[3].m_num;
lean_object* v_bs_657_ = stack[4].m_obj;
lean_object* v_res_671_;
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_653_, v___x_654_, v_sz_655_, v_i_656_, v_bs_657_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_672_, lean_object* v___x_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_bs_676_){
_start:
{
size_t v_sz_boxed_677_; size_t v_i_boxed_678_; lean_object* v_res_679_; 
v_sz_boxed_677_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_678_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_679_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_672_, v___x_673_, v_sz_boxed_677_, v_i_boxed_678_, v_bs_676_);
lean_dec_ref(v___x_673_);
return v_res_679_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object* v_infos_686_, lean_object* v_numParams_687_, lean_object* v___x_688_, lean_object* v_name_689_, lean_object* v_levels_690_, lean_object* v_args_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; size_t v_sz_716_; size_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_705_ = lean_array_get_size(v_infos_686_);
v___x_706_ = lean_nat_sub(v_numParams_687_, v___x_705_);
lean_inc(v___x_688_);
lean_inc_ref(v_args_691_);
v___x_707_ = l_Array_toSubarray___redArg(v_args_691_, v___x_688_, v___x_706_);
v___x_708_ = lean_array_get_size(v_args_691_);
v___x_709_ = l_Array_toSubarray___redArg(v_args_691_, v_numParams_687_, v___x_708_);
lean_inc_n(v_name_689_, 2);
v___x_710_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_689_);
lean_inc_n(v_levels_690_, 3);
lean_inc(v___x_710_);
v___x_711_ = l_Lean_mkConst(v___x_710_, v_levels_690_);
v___x_712_ = l_Subarray_copy___redArg(v___x_707_);
v___x_713_ = l_Lean_mkAppN(v___x_711_, v___x_712_);
lean_inc_ref(v___x_709_);
v___x_714_ = l_Subarray_copy___redArg(v___x_709_);
v___x_715_ = l_Lean_mkAppN(v___x_713_, v___x_714_);
v_sz_716_ = lean_array_size(v_infos_686_);
v___x_717_ = ((size_t)0ULL);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_690_, v___x_712_, v_sz_716_, v___x_717_, v_infos_686_);
v___x_719_ = l_Lean_mkConst(v_name_689_, v_levels_690_);
lean_inc_ref(v___x_712_);
v___x_720_ = l_Array_append___redArg(v___x_712_, v___x_718_);
lean_dec_ref(v___x_718_);
v___x_721_ = l_Array_append___redArg(v___x_720_, v___x_714_);
v___x_722_ = l_Lean_mkAppN(v___x_719_, v___x_721_);
lean_dec_ref(v___x_721_);
v___x_723_ = l_Lean_Meta_mkEq(v___x_715_, v___x_722_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_783_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_783_ == 0)
{
v___x_726_ = v___x_723_;
v_isShared_727_ = v_isSharedCheck_783_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_783_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set_tag(v___x_726_, 1);
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_782_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_730_ = 0;
v___x_731_ = lean_box(0);
v___x_732_ = l_Lean_Meta_mkFreshExprMVar(v___x_729_, v___x_730_, v___x_731_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_Expr_mvarId_x21(v_a_733_);
v___x_735_ = l_Lean_Meta_getEqnsFor_x3f(v___x_710_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
if (lean_obj_tag(v_a_736_) == 1)
{
lean_object* v_val_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_val_737_ = lean_ctor_get(v_a_736_, 0);
lean_inc(v_val_737_);
lean_dec_ref_known(v_a_736_, 1);
v___x_738_ = lean_array_get_size(v_val_737_);
v___x_739_ = lean_unsigned_to_nat(1u);
v___x_740_ = lean_nat_dec_eq(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v_val_737_);
lean_dec(v___x_734_);
lean_dec(v_a_733_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_709_);
lean_dec(v_levels_690_);
lean_dec(v_name_689_);
lean_dec(v___x_688_);
v___y_699_ = v___y_693_;
v___y_700_ = v___y_694_;
v___y_701_ = v___y_695_;
v___y_702_ = v___y_696_;
goto v___jp_698_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_741_ = lean_array_fget(v_val_737_, v___x_688_);
lean_dec(v___x_688_);
lean_dec(v_val_737_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3));
v___x_743_ = l_Lean_Name_append(v_name_689_, v___x_742_);
lean_inc(v_levels_690_);
v___x_744_ = l_Lean_mkConst(v___x_743_, v_levels_690_);
v___x_745_ = l_Lean_mkConst(v___x_741_, v_levels_690_);
v___x_746_ = l_Lean_mkAppN(v___x_745_, v___x_712_);
v___x_747_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_709_, v___x_746_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; uint8_t v___x_749_; lean_object* v___x_750_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = 0;
v___x_750_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_734_, v___x_744_, v___x_749_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_751_, v_a_748_, v___y_694_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v___x_753_; 
lean_dec_ref_known(v___x_752_, 1);
v___x_753_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_733_, v___y_694_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = l_Array_append___redArg(v___x_712_, v___x_714_);
lean_dec_ref(v___x_714_);
v___x_756_ = 1;
v___x_757_ = l_Lean_Meta_mkLambdaFVars(v___x_755_, v_a_754_, v___x_749_, v___x_740_, v___x_749_, v___x_740_, v___x_756_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec_ref(v___x_755_);
return v___x_757_;
}
else
{
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
return v___x_753_;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_733_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v_a_758_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_752_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_752_);
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
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_a_748_);
lean_dec(v_a_733_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
v_a_766_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_750_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_750_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_dec_ref(v___x_744_);
lean_dec(v___x_734_);
lean_dec(v_a_733_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
return v___x_747_;
}
}
}
else
{
lean_dec(v_a_736_);
lean_dec(v___x_734_);
lean_dec(v_a_733_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_709_);
lean_dec(v_levels_690_);
lean_dec(v_name_689_);
lean_dec(v___x_688_);
v___y_699_ = v___y_693_;
v___y_700_ = v___y_694_;
v___y_701_ = v___y_695_;
v___y_702_ = v___y_696_;
goto v___jp_698_;
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec(v___x_734_);
lean_dec(v_a_733_);
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
lean_dec_ref(v___x_709_);
lean_dec(v_levels_690_);
lean_dec(v_name_689_);
lean_dec(v___x_688_);
v_a_774_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_735_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_735_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
else
{
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
lean_dec(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec(v_levels_690_);
lean_dec(v_name_689_);
lean_dec(v___x_688_);
return v___x_732_;
}
}
}
}
else
{
lean_dec_ref(v___x_714_);
lean_dec_ref(v___x_712_);
lean_dec(v___x_710_);
lean_dec_ref(v___x_709_);
lean_dec(v_levels_690_);
lean_dec(v_name_689_);
lean_dec(v___x_688_);
return v___x_723_;
}
v___jp_698_:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
v___x_704_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_703_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
return v___x_704_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_686_ = stack[0].m_obj;
lean_object* v_numParams_687_ = stack[1].m_obj;
lean_object* v___x_688_ = stack[2].m_obj;
lean_object* v_name_689_ = stack[3].m_obj;
lean_object* v_levels_690_ = stack[4].m_obj;
lean_object* v_args_691_ = stack[5].m_obj;
lean_object* v_x_692_ = stack[6].m_obj;
lean_object* v___y_693_ = stack[7].m_obj;
lean_object* v___y_694_ = stack[8].m_obj;
lean_object* v___y_695_ = stack[9].m_obj;
lean_object* v___y_696_ = stack[10].m_obj;
lean_object* v_res_784_;
v_res_784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_686_, v_numParams_687_, v___x_688_, v_name_689_, v_levels_690_, v_args_691_, v_x_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
stack->m_obj
 = v_res_784_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object* v_infos_785_, lean_object* v_numParams_786_, lean_object* v___x_787_, lean_object* v_name_788_, lean_object* v_levels_789_, lean_object* v_args_790_, lean_object* v_x_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_785_, v_numParams_786_, v___x_787_, v_name_788_, v_levels_789_, v_args_790_, v_x_791_, v___y_792_, v___y_793_, v___y_794_, v___y_795_);
lean_dec(v___y_795_);
lean_dec_ref(v___y_794_);
lean_dec(v___y_793_);
lean_dec_ref(v___y_792_);
lean_dec_ref(v_x_791_);
return v_res_797_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0(void){
_start:
{
lean_object* v___x_798_; double v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_float_of_nat(v___x_798_);
return v___x_799_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v_ref_810_; lean_object* v___x_811_; lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_857_; 
v_ref_810_ = lean_ctor_get(v___y_807_, 2);
v___x_811_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_857_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_857_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_857_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v_traceState_817_; lean_object* v_env_818_; lean_object* v_nextMacroScope_819_; lean_object* v_ngen_820_; lean_object* v_auxDeclNGen_821_; lean_object* v_cache_822_; lean_object* v_recordedDeps_823_; lean_object* v_messages_824_; lean_object* v_infoState_825_; lean_object* v_snapshotTasks_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_856_; 
v___x_816_ = lean_st_ref_take(v___y_808_);
v_traceState_817_ = lean_ctor_get(v___x_816_, 4);
v_env_818_ = lean_ctor_get(v___x_816_, 0);
v_nextMacroScope_819_ = lean_ctor_get(v___x_816_, 1);
v_ngen_820_ = lean_ctor_get(v___x_816_, 2);
v_auxDeclNGen_821_ = lean_ctor_get(v___x_816_, 3);
v_cache_822_ = lean_ctor_get(v___x_816_, 5);
v_recordedDeps_823_ = lean_ctor_get(v___x_816_, 6);
v_messages_824_ = lean_ctor_get(v___x_816_, 7);
v_infoState_825_ = lean_ctor_get(v___x_816_, 8);
v_snapshotTasks_826_ = lean_ctor_get(v___x_816_, 9);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_856_ == 0)
{
v___x_828_ = v___x_816_;
v_isShared_829_ = v_isSharedCheck_856_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_snapshotTasks_826_);
lean_inc(v_infoState_825_);
lean_inc(v_messages_824_);
lean_inc(v_recordedDeps_823_);
lean_inc(v_cache_822_);
lean_inc(v_traceState_817_);
lean_inc(v_auxDeclNGen_821_);
lean_inc(v_ngen_820_);
lean_inc(v_nextMacroScope_819_);
lean_inc(v_env_818_);
lean_dec(v___x_816_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_856_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
uint64_t v_tid_830_; lean_object* v_traces_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_855_; 
v_tid_830_ = lean_ctor_get_uint64(v_traceState_817_, sizeof(void*)*1);
v_traces_831_ = lean_ctor_get(v_traceState_817_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v_traceState_817_);
if (v_isSharedCheck_855_ == 0)
{
v___x_833_ = v_traceState_817_;
v_isShared_834_ = v_isSharedCheck_855_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_traces_831_);
lean_dec(v_traceState_817_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_855_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; double v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_835_ = lean_box(0);
v___x_836_ = lean_box(0);
v___x_837_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_838_ = 0;
v___x_839_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_840_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_840_, 0, v_cls_803_);
lean_ctor_set(v___x_840_, 1, v___x_836_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
lean_ctor_set_float(v___x_840_, sizeof(void*)*3, v___x_837_);
lean_ctor_set_float(v___x_840_, sizeof(void*)*3 + 8, v___x_837_);
lean_ctor_set_uint8(v___x_840_, sizeof(void*)*3 + 16, v___x_838_);
v___x_841_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_842_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v_a_812_);
lean_ctor_set(v___x_842_, 2, v___x_841_);
lean_inc(v_ref_810_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_ref_810_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = l_Lean_PersistentArray_push___redArg(v_traces_831_, v___x_843_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_844_);
v___x_846_ = v___x_833_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_844_);
lean_ctor_set_uint64(v_reuseFailAlloc_854_, sizeof(void*)*1, v_tid_830_);
v___x_846_ = v_reuseFailAlloc_854_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_848_; 
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 4, v___x_846_);
v___x_848_ = v___x_828_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_env_818_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_nextMacroScope_819_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_ngen_820_);
lean_ctor_set(v_reuseFailAlloc_853_, 3, v_auxDeclNGen_821_);
lean_ctor_set(v_reuseFailAlloc_853_, 4, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_853_, 5, v_cache_822_);
lean_ctor_set(v_reuseFailAlloc_853_, 6, v_recordedDeps_823_);
lean_ctor_set(v_reuseFailAlloc_853_, 7, v_messages_824_);
lean_ctor_set(v_reuseFailAlloc_853_, 8, v_infoState_825_);
lean_ctor_set(v_reuseFailAlloc_853_, 9, v_snapshotTasks_826_);
v___x_848_ = v_reuseFailAlloc_853_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_st_ref_put(v___y_808_, v___x_848_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_835_);
v___x_851_ = v___x_814_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_835_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_803_ = stack[0].m_obj;
lean_object* v_msg_804_ = stack[1].m_obj;
lean_object* v___y_805_ = stack[2].m_obj;
lean_object* v___y_806_ = stack[3].m_obj;
lean_object* v___y_807_ = stack[4].m_obj;
lean_object* v___y_808_ = stack[5].m_obj;
lean_object* v_res_858_;
v_res_858_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_803_, v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
stack->m_obj
 = v_res_858_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object* v_cls_859_, lean_object* v_msg_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_859_, v_msg_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_866_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_875_ = l_Lean_Name_append(v___x_874_, v___x_873_);
return v___x_875_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_877_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5));
v___x_878_ = l_Lean_stringToMessageData(v___x_877_);
return v___x_878_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object* v_infos_879_, lean_object* v_levels_880_, lean_object* v_as_881_, size_t v_sz_882_, size_t v_i_883_, lean_object* v_b_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = lean_usize_dec_lt(v_i_883_, v_sz_882_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v_levels_880_);
lean_dec_ref(v_infos_879_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_b_884_);
return v___x_891_;
}
else
{
lean_object* v_a_892_; lean_object* v_toConstantVal_893_; lean_object* v_numParams_894_; lean_object* v_name_895_; lean_object* v_levelParams_896_; lean_object* v_type_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___f_900_; uint8_t v___x_901_; lean_object* v___x_902_; 
v_a_892_ = lean_array_uget_borrowed(v_as_881_, v_i_883_);
v_toConstantVal_893_ = lean_ctor_get(v_a_892_, 0);
v_numParams_894_ = lean_ctor_get(v_a_892_, 1);
v_name_895_ = lean_ctor_get(v_toConstantVal_893_, 0);
v_levelParams_896_ = lean_ctor_get(v_toConstantVal_893_, 1);
v_type_897_ = lean_ctor_get(v_toConstantVal_893_, 2);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_box(0);
lean_inc(v_levels_880_);
lean_inc(v_name_895_);
lean_inc(v_numParams_894_);
lean_inc_ref(v_infos_879_);
v___f_900_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed), 12, 5);
lean_closure_set(v___f_900_, 0, v_infos_879_);
lean_closure_set(v___f_900_, 1, v_numParams_894_);
lean_closure_set(v___f_900_, 2, v___x_898_);
lean_closure_set(v___f_900_, 3, v_name_895_);
lean_closure_set(v___f_900_, 4, v_levels_880_);
v___x_901_ = 0;
lean_inc_ref(v_type_897_);
v___x_902_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_897_, v___f_900_, v___x_901_, v___x_901_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v_toCold_938_; lean_object* v_options_939_; uint8_t v_hasTrace_940_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v_toCold_938_ = lean_ctor_get(v___y_887_, 0);
v_options_939_ = lean_ctor_get(v_toCold_938_, 2);
v_hasTrace_940_ = lean_ctor_get_uint8(v_options_939_, sizeof(void*)*1);
if (v_hasTrace_940_ == 0)
{
v___y_905_ = v___y_885_;
v___y_906_ = v___y_886_;
v___y_907_ = v___y_887_;
v___y_908_ = v___y_888_;
goto v___jp_904_;
}
else
{
lean_object* v_inheritedTraceOptions_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_inheritedTraceOptions_941_ = lean_ctor_get(v_toCold_938_, 11);
v___x_942_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_943_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_944_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_941_, v_options_939_, v___x_943_);
if (v___x_944_ == 0)
{
v___y_905_ = v___y_885_;
v___y_906_ = v___y_886_;
v___y_907_ = v___y_887_;
v___y_908_ = v___y_888_;
goto v___jp_904_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_945_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
lean_inc(v_a_903_);
v___x_946_ = l_Lean_MessageData_ofExpr(v_a_903_);
v___x_947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_942_, v___x_947_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_dec_ref_known(v___x_948_, 1);
v___y_905_ = v___y_885_;
v___y_906_ = v___y_886_;
v___y_907_ = v___y_887_;
v___y_908_ = v___y_888_;
goto v___jp_904_;
}
else
{
lean_dec(v_a_903_);
lean_dec(v_levels_880_);
lean_dec_ref(v_infos_879_);
return v___x_948_;
}
}
}
v___jp_904_:
{
lean_object* v___x_909_; 
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
lean_inc(v_a_903_);
v___x_909_ = lean_infer_type(v_a_903_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
lean_inc(v_name_895_);
v___x_911_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_895_);
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_913_ = l_Lean_Name_append(v___x_911_, v___x_912_);
v___x_914_ = lean_box(0);
lean_inc(v_levelParams_896_);
v___x_915_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_913_, v_levelParams_896_, v_a_910_, v_a_903_, v___x_914_, v___y_908_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v_a_916_);
v___x_918_ = l_Lean_addDecl(v___x_917_, v___x_901_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_918_) == 0)
{
size_t v___x_919_; size_t v___x_920_; 
lean_dec_ref_known(v___x_918_, 1);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = lean_usize_add(v_i_883_, v___x_919_);
v_i_883_ = v___x_920_;
v_b_884_ = v___x_899_;
goto _start;
}
else
{
lean_dec(v_levels_880_);
lean_dec_ref(v_infos_879_);
return v___x_918_;
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_levels_880_);
lean_dec_ref(v_infos_879_);
v_a_922_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_915_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_915_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_a_903_);
lean_dec(v_levels_880_);
lean_dec_ref(v_infos_879_);
v_a_930_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_909_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_909_);
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
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_levels_880_);
lean_dec_ref(v_infos_879_);
v_a_949_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_902_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_902_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_879_ = stack[0].m_obj;
lean_object* v_levels_880_ = stack[1].m_obj;
lean_object* v_as_881_ = stack[2].m_obj;
size_t v_sz_882_ = stack[3].m_num;
size_t v_i_883_ = stack[4].m_num;
lean_object* v_b_884_ = stack[5].m_obj;
lean_object* v___y_885_ = stack[6].m_obj;
lean_object* v___y_886_ = stack[7].m_obj;
lean_object* v___y_887_ = stack[8].m_obj;
lean_object* v___y_888_ = stack[9].m_obj;
lean_object* v_res_957_;
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_879_, v_levels_880_, v_as_881_, v_sz_882_, v_i_883_, v_b_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
stack->m_obj
 = v_res_957_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object* v_infos_958_, lean_object* v_levels_959_, lean_object* v_as_960_, lean_object* v_sz_961_, lean_object* v_i_962_, lean_object* v_b_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_){
_start:
{
size_t v_sz_boxed_969_; size_t v_i_boxed_970_; lean_object* v_res_971_; 
v_sz_boxed_969_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v_i_boxed_970_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_958_, v_levels_959_, v_as_960_, v_sz_boxed_969_, v_i_boxed_970_, v_b_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec_ref(v_as_960_);
return v_res_971_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object* v_infos_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_toConstantVal_981_; lean_object* v_levelParams_982_; lean_object* v___x_983_; lean_object* v_levels_984_; lean_object* v___x_985_; size_t v_sz_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_978_ = l_Lean_instInhabitedInductiveVal_default;
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_array_get_borrowed(v___x_978_, v_infos_972_, v___x_979_);
v_toConstantVal_981_ = lean_ctor_get(v___x_980_, 0);
v_levelParams_982_ = lean_ctor_get(v_toConstantVal_981_, 1);
v___x_983_ = lean_box(0);
lean_inc(v_levelParams_982_);
v_levels_984_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_982_, v___x_983_);
v___x_985_ = lean_box(0);
v_sz_986_ = lean_array_size(v_infos_972_);
v___x_987_ = ((size_t)0ULL);
lean_inc_ref(v_infos_972_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_972_, v_levels_984_, v_infos_972_, v_sz_986_, v___x_987_, v___x_985_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec_ref(v_infos_972_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_988_, 0);
lean_dec(v_unused_996_);
v___x_990_ = v___x_988_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_dec(v___x_988_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 0, v___x_985_);
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_985_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
else
{
return v___x_988_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_972_ = stack[0].m_obj;
lean_object* v_a_973_ = stack[1].m_obj;
lean_object* v_a_974_ = stack[2].m_obj;
lean_object* v_a_975_ = stack[3].m_obj;
lean_object* v_a_976_ = stack[4].m_obj;
lean_object* v_res_997_;
v_res_997_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
stack->m_obj
 = v_res_997_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object* v_infos_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
return v_res_1004_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object* v_00_u03b1_1005_, lean_object* v_msg_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1006_ = stack[1].m_obj;
lean_object* v___y_1007_ = stack[2].m_obj;
lean_object* v___y_1008_ = stack[3].m_obj;
lean_object* v___y_1009_ = stack[4].m_obj;
lean_object* v___y_1010_ = stack[5].m_obj;
lean_object* v_res_1013_;
v_res_1013_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_box(0), v_msg_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
stack->m_obj
 = v_res_1013_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_msg_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_1014_, v_msg_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
return v_res_1021_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object* v_inst_1022_, lean_object* v_R_1023_, lean_object* v_a_1024_, lean_object* v_b_1025_, lean_object* v_c_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_1024_, v_b_1025_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1024_ = stack[2].m_obj;
lean_object* v_b_1025_ = stack[3].m_obj;
lean_object* v___y_1027_ = stack[5].m_obj;
lean_object* v___y_1028_ = stack[6].m_obj;
lean_object* v___y_1029_ = stack[7].m_obj;
lean_object* v___y_1030_ = stack[8].m_obj;
lean_object* v_res_1033_;
v_res_1033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_box(0), lean_box(0), v_a_1024_, v_b_1025_, lean_box(0), v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
stack->m_obj
 = v_res_1033_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object* v_inst_1034_, lean_object* v_R_1035_, lean_object* v_a_1036_, lean_object* v_b_1037_, lean_object* v_c_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_1034_, v_R_1035_, v_a_1036_, v_b_1037_, v_c_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
return v_res_1044_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object* v_mvarId_1045_, lean_object* v_val_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_1045_, v_val_1046_, v___y_1048_);
return v___x_1052_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1045_ = stack[0].m_obj;
lean_object* v_val_1046_ = stack[1].m_obj;
lean_object* v___y_1047_ = stack[2].m_obj;
lean_object* v___y_1048_ = stack[3].m_obj;
lean_object* v___y_1049_ = stack[4].m_obj;
lean_object* v___y_1050_ = stack[5].m_obj;
lean_object* v_res_1053_;
v_res_1053_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1045_, v_val_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
stack->m_obj
 = v_res_1053_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object* v_mvarId_1054_, lean_object* v_val_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1054_, v_val_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object* v_00_u03b2_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_1063_, v_x_1064_, v_x_1065_);
return v___x_1066_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1067_, lean_object* v_x_1068_, size_t v_x_1069_, size_t v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_1068_, v_x_1069_, v_x_1070_, v_x_1071_, v_x_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1068_ = stack[1].m_obj;
size_t v_x_1069_ = stack[2].m_num;
size_t v_x_1070_ = stack[3].m_num;
lean_object* v_x_1071_ = stack[4].m_obj;
lean_object* v_x_1072_ = stack[5].m_obj;
lean_object* v_res_1074_;
v_res_1074_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_box(0), v_x_1068_, v_x_1069_, v_x_1070_, v_x_1071_, v_x_1072_);
stack->m_obj
 = v_res_1074_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
size_t v_x_10401__boxed_1081_; size_t v_x_10402__boxed_1082_; lean_object* v_res_1083_; 
v_x_10401__boxed_1081_ = lean_unbox_usize(v_x_1077_);
lean_dec(v_x_1077_);
v_x_10402__boxed_1082_ = lean_unbox_usize(v_x_1078_);
lean_dec(v_x_1078_);
v_res_1083_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_1075_, v_x_1076_, v_x_10401__boxed_1081_, v_x_10402__boxed_1082_, v_x_1079_, v_x_1080_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1084_, lean_object* v_n_1085_, lean_object* v_k_1086_, lean_object* v_v_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v_n_1085_, v_k_1086_, v_v_1087_);
return v___x_1088_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1089_, size_t v_depth_1090_, lean_object* v_keys_1091_, lean_object* v_vals_1092_, lean_object* v_heq_1093_, lean_object* v_i_1094_, lean_object* v_entries_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_1090_, v_keys_1091_, v_vals_1092_, v_i_1094_, v_entries_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1090_ = stack[1].m_num;
lean_object* v_keys_1091_ = stack[2].m_obj;
lean_object* v_vals_1092_ = stack[3].m_obj;
lean_object* v_i_1094_ = stack[5].m_obj;
lean_object* v_entries_1095_ = stack[6].m_obj;
lean_object* v_res_1097_;
v_res_1097_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_box(0), v_depth_1090_, v_keys_1091_, v_vals_1092_, lean_box(0), v_i_1094_, v_entries_1095_);
stack->m_obj
 = v_res_1097_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1098_, lean_object* v_depth_1099_, lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_heq_1102_, lean_object* v_i_1103_, lean_object* v_entries_1104_){
_start:
{
size_t v_depth_boxed_1105_; lean_object* v_res_1106_; 
v_depth_boxed_1105_ = lean_unbox_usize(v_depth_1099_);
lean_dec(v_depth_1099_);
v_res_1106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(v_00_u03b2_1098_, v_depth_boxed_1105_, v_keys_1100_, v_vals_1101_, v_heq_1102_, v_i_1103_, v_entries_1104_);
lean_dec_ref(v_vals_1101_);
lean_dec_ref(v_keys_1100_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_x_1108_, v_x_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object* v_e_1113_, lean_object* v___y_1114_){
_start:
{
uint8_t v___x_1116_; 
v___x_1116_ = l_Lean_Expr_hasMVar(v_e_1113_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_e_1113_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v_mctx_1119_; lean_object* v___x_1120_; lean_object* v_fst_1121_; lean_object* v_snd_1122_; lean_object* v___x_1123_; lean_object* v_cache_1124_; lean_object* v_zetaDeltaFVarIds_1125_; lean_object* v_postponed_1126_; lean_object* v_diag_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v___x_1118_ = lean_st_ref_get(v___y_1114_);
v_mctx_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc_ref(v_mctx_1119_);
lean_dec(v___x_1118_);
v___x_1120_ = l_Lean_instantiateMVarsCore(v_mctx_1119_, v_e_1113_);
v_fst_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_fst_1121_);
v_snd_1122_ = lean_ctor_get(v___x_1120_, 1);
lean_inc(v_snd_1122_);
lean_dec_ref(v___x_1120_);
v___x_1123_ = lean_st_ref_take(v___y_1114_);
v_cache_1124_ = lean_ctor_get(v___x_1123_, 1);
v_zetaDeltaFVarIds_1125_ = lean_ctor_get(v___x_1123_, 2);
v_postponed_1126_ = lean_ctor_get(v___x_1123_, 3);
v_diag_1127_ = lean_ctor_get(v___x_1123_, 4);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v___x_1123_, 0);
lean_dec(v_unused_1137_);
v___x_1129_ = v___x_1123_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_diag_1127_);
lean_inc(v_postponed_1126_);
lean_inc(v_zetaDeltaFVarIds_1125_);
lean_inc(v_cache_1124_);
lean_dec(v___x_1123_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_snd_1122_);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_snd_1122_);
lean_ctor_set(v_reuseFailAlloc_1135_, 1, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1135_, 2, v_zetaDeltaFVarIds_1125_);
lean_ctor_set(v_reuseFailAlloc_1135_, 3, v_postponed_1126_);
lean_ctor_set(v_reuseFailAlloc_1135_, 4, v_diag_1127_);
v___x_1132_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_st_ref_put(v___y_1114_, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v_fst_1121_);
return v___x_1134_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1113_ = stack[0].m_obj;
lean_object* v___y_1114_ = stack[1].m_obj;
lean_object* v_res_1138_;
v_res_1138_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1113_, v___y_1114_);
stack->m_obj
 = v_res_1138_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_e_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1139_, v___y_1140_);
lean_dec(v___y_1140_);
return v_res_1142_;
}
}
lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_e_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1143_, v___y_1147_);
return v___x_1151_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1143_ = stack[0].m_obj;
lean_object* v___y_1144_ = stack[1].m_obj;
lean_object* v___y_1145_ = stack[2].m_obj;
lean_object* v___y_1146_ = stack[3].m_obj;
lean_object* v___y_1147_ = stack[4].m_obj;
lean_object* v___y_1148_ = stack[5].m_obj;
lean_object* v___y_1149_ = stack[6].m_obj;
lean_object* v_res_1152_;
v_res_1152_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
stack->m_obj
 = v_res_1152_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_e_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1161_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object* v_k_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v_b_1165_, lean_object* v_c_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
lean_object* v___x_1172_; 
lean_inc(v___y_1170_);
lean_inc_ref(v___y_1169_);
lean_inc(v___y_1168_);
lean_inc_ref(v___y_1167_);
lean_inc(v___y_1164_);
lean_inc_ref(v___y_1163_);
v___x_1172_ = lean_apply_9(v_k_1162_, v_b_1165_, v_c_1166_, v___y_1163_, v___y_1164_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, lean_box(0));
return v___x_1172_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1162_ = stack[0].m_obj;
lean_object* v___y_1163_ = stack[1].m_obj;
lean_object* v___y_1164_ = stack[2].m_obj;
lean_object* v_b_1165_ = stack[3].m_obj;
lean_object* v_c_1166_ = stack[4].m_obj;
lean_object* v___y_1167_ = stack[5].m_obj;
lean_object* v___y_1168_ = stack[6].m_obj;
lean_object* v___y_1169_ = stack[7].m_obj;
lean_object* v___y_1170_ = stack[8].m_obj;
lean_object* v_res_1173_;
v_res_1173_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1162_, v___y_1163_, v___y_1164_, v_b_1165_, v_c_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
stack->m_obj
 = v_res_1173_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object* v_k_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v_b_1177_, lean_object* v_c_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1174_, v___y_1175_, v___y_1176_, v_b_1177_, v_c_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
return v_res_1184_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_type_1185_, lean_object* v_k_1186_, uint8_t v_cleanupAnnotations_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___f_1195_; uint8_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_inc(v___y_1189_);
lean_inc_ref(v___y_1188_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1195_, 0, v_k_1186_);
lean_closure_set(v___f_1195_, 1, v___y_1188_);
lean_closure_set(v___f_1195_, 2, v___y_1189_);
v___x_1196_ = 0;
v___x_1197_ = lean_box(0);
v___x_1198_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1196_, v___x_1197_, v_type_1185_, v___f_1195_, v_cleanupAnnotations_1187_, v___x_1196_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
if (lean_obj_tag(v___x_1198_) == 0)
{
return v___x_1198_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1185_ = stack[0].m_obj;
lean_object* v_k_1186_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_1187_ = stack[2].m_num;
lean_object* v___y_1188_ = stack[3].m_obj;
lean_object* v___y_1189_ = stack[4].m_obj;
lean_object* v___y_1190_ = stack[5].m_obj;
lean_object* v___y_1191_ = stack[6].m_obj;
lean_object* v___y_1192_ = stack[7].m_obj;
lean_object* v___y_1193_ = stack[8].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1185_, v_k_1186_, v_cleanupAnnotations_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_type_1208_, lean_object* v_k_1209_, lean_object* v_cleanupAnnotations_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1218_; lean_object* v_res_1219_; 
v_cleanupAnnotations_boxed_1218_ = lean_unbox(v_cleanupAnnotations_1210_);
v_res_1219_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1208_, v_k_1209_, v_cleanupAnnotations_boxed_1218_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1219_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_00_u03b1_1220_, lean_object* v_type_1221_, lean_object* v_k_1222_, uint8_t v_cleanupAnnotations_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1221_, v_k_1222_, v_cleanupAnnotations_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1221_ = stack[1].m_obj;
lean_object* v_k_1222_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1223_ = stack[3].m_num;
lean_object* v___y_1224_ = stack[4].m_obj;
lean_object* v___y_1225_ = stack[5].m_obj;
lean_object* v___y_1226_ = stack[6].m_obj;
lean_object* v___y_1227_ = stack[7].m_obj;
lean_object* v___y_1228_ = stack[8].m_obj;
lean_object* v___y_1229_ = stack[9].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_box(0), v_type_1221_, v_k_1222_, v_cleanupAnnotations_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_00_u03b1_1233_, lean_object* v_type_1234_, lean_object* v_k_1235_, lean_object* v_cleanupAnnotations_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1244_; lean_object* v_res_1245_; 
v_cleanupAnnotations_boxed_1244_ = lean_unbox(v_cleanupAnnotations_1236_);
v_res_1245_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_1233_, v_type_1234_, v_k_1235_, v_cleanupAnnotations_boxed_1244_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1245_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_name_1246_, lean_object* v_levelParams_1247_, lean_object* v_type_1248_, lean_object* v_value_1249_, lean_object* v_hints_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; uint8_t v___y_1255_; uint8_t v___y_1262_; lean_object* v_env_1265_; uint8_t v___x_1266_; 
v___x_1253_ = lean_st_ref_get(v___y_1251_);
v_env_1265_ = lean_ctor_get(v___x_1253_, 0);
lean_inc_ref_n(v_env_1265_, 2);
lean_dec(v___x_1253_);
v___x_1266_ = l_Lean_Environment_hasUnsafe(v_env_1265_, v_type_1248_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; 
v___x_1267_ = l_Lean_Environment_hasUnsafe(v_env_1265_, v_value_1249_);
v___y_1262_ = v___x_1267_;
goto v___jp_1261_;
}
else
{
lean_dec_ref(v_env_1265_);
v___y_1262_ = v___x_1266_;
goto v___jp_1261_;
}
v___jp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_inc(v_name_1246_);
v___x_1256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1256_, 0, v_name_1246_);
lean_ctor_set(v___x_1256_, 1, v_levelParams_1247_);
lean_ctor_set(v___x_1256_, 2, v_type_1248_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_name_1246_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1259_, 0, v___x_1256_);
lean_ctor_set(v___x_1259_, 1, v_value_1249_);
lean_ctor_set(v___x_1259_, 2, v_hints_1250_);
lean_ctor_set(v___x_1259_, 3, v___x_1258_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*4, v___y_1255_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
v___jp_1261_:
{
if (v___y_1262_ == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = 1;
v___y_1255_ = v___x_1263_;
goto v___jp_1254_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = 0;
v___y_1255_ = v___x_1264_;
goto v___jp_1254_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1246_ = stack[0].m_obj;
lean_object* v_levelParams_1247_ = stack[1].m_obj;
lean_object* v_type_1248_ = stack[2].m_obj;
lean_object* v_value_1249_ = stack[3].m_obj;
lean_object* v_hints_1250_ = stack[4].m_obj;
lean_object* v___y_1251_ = stack[5].m_obj;
lean_object* v_res_1268_;
v_res_1268_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1246_, v_levelParams_1247_, v_type_1248_, v_value_1249_, v_hints_1250_, v___y_1251_);
stack->m_obj
 = v_res_1268_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1269_, lean_object* v_levelParams_1270_, lean_object* v_type_1271_, lean_object* v_value_1272_, lean_object* v_hints_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1269_, v_levelParams_1270_, v_type_1271_, v_value_1272_, v_hints_1273_, v___y_1274_);
lean_dec(v___y_1274_);
return v_res_1276_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1277_, lean_object* v_levelParams_1278_, lean_object* v_type_1279_, lean_object* v_value_1280_, lean_object* v_hints_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1277_, v_levelParams_1278_, v_type_1279_, v_value_1280_, v_hints_1281_, v___y_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1277_ = stack[0].m_obj;
lean_object* v_levelParams_1278_ = stack[1].m_obj;
lean_object* v_type_1279_ = stack[2].m_obj;
lean_object* v_value_1280_ = stack[3].m_obj;
lean_object* v_hints_1281_ = stack[4].m_obj;
lean_object* v___y_1282_ = stack[5].m_obj;
lean_object* v___y_1283_ = stack[6].m_obj;
lean_object* v___y_1284_ = stack[7].m_obj;
lean_object* v___y_1285_ = stack[8].m_obj;
lean_object* v___y_1286_ = stack[9].m_obj;
lean_object* v___y_1287_ = stack[10].m_obj;
lean_object* v_res_1290_;
v_res_1290_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1277_, v_levelParams_1278_, v_type_1279_, v_value_1280_, v_hints_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
stack->m_obj
 = v_res_1290_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1291_, lean_object* v_levelParams_1292_, lean_object* v_type_1293_, lean_object* v_value_1294_, lean_object* v_hints_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1291_, v_levelParams_1292_, v_type_1293_, v_value_1294_, v_hints_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
return v_res_1303_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1304_, lean_object* v_maxFVars_x3f_1305_, lean_object* v_k_1306_, uint8_t v_cleanupAnnotations_1307_, uint8_t v_whnfType_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___f_1316_; lean_object* v___x_1317_; 
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
v___f_1316_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1316_, 0, v_k_1306_);
lean_closure_set(v___f_1316_, 1, v___y_1309_);
lean_closure_set(v___f_1316_, 2, v___y_1310_);
v___x_1317_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1304_, v_maxFVars_x3f_1305_, v___f_1316_, v_cleanupAnnotations_1307_, v_whnfType_1308_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1317_) == 0)
{
return v___x_1317_;
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1317_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1317_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1304_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_1305_ = stack[1].m_obj;
lean_object* v_k_1306_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1307_ = stack[3].m_num;
uint8_t v_whnfType_1308_ = stack[4].m_num;
lean_object* v___y_1309_ = stack[5].m_obj;
lean_object* v___y_1310_ = stack[6].m_obj;
lean_object* v___y_1311_ = stack[7].m_obj;
lean_object* v___y_1312_ = stack[8].m_obj;
lean_object* v___y_1313_ = stack[9].m_obj;
lean_object* v___y_1314_ = stack[10].m_obj;
lean_object* v_res_1326_;
v_res_1326_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1304_, v_maxFVars_x3f_1305_, v_k_1306_, v_cleanupAnnotations_1307_, v_whnfType_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
stack->m_obj
 = v_res_1326_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1327_, lean_object* v_maxFVars_x3f_1328_, lean_object* v_k_1329_, lean_object* v_cleanupAnnotations_1330_, lean_object* v_whnfType_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1339_; uint8_t v_whnfType_boxed_1340_; lean_object* v_res_1341_; 
v_cleanupAnnotations_boxed_1339_ = lean_unbox(v_cleanupAnnotations_1330_);
v_whnfType_boxed_1340_ = lean_unbox(v_whnfType_1331_);
v_res_1341_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1327_, v_maxFVars_x3f_1328_, v_k_1329_, v_cleanupAnnotations_boxed_1339_, v_whnfType_boxed_1340_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1341_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1342_, lean_object* v_type_1343_, lean_object* v_maxFVars_x3f_1344_, lean_object* v_k_1345_, uint8_t v_cleanupAnnotations_1346_, uint8_t v_whnfType_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1343_, v_maxFVars_x3f_1344_, v_k_1345_, v_cleanupAnnotations_1346_, v_whnfType_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
return v___x_1355_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_1343_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_1344_ = stack[2].m_obj;
lean_object* v_k_1345_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_1346_ = stack[4].m_num;
uint8_t v_whnfType_1347_ = stack[5].m_num;
lean_object* v___y_1348_ = stack[6].m_obj;
lean_object* v___y_1349_ = stack[7].m_obj;
lean_object* v___y_1350_ = stack[8].m_obj;
lean_object* v___y_1351_ = stack[9].m_obj;
lean_object* v___y_1352_ = stack[10].m_obj;
lean_object* v___y_1353_ = stack[11].m_obj;
lean_object* v_res_1356_;
v_res_1356_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_box(0), v_type_1343_, v_maxFVars_x3f_1344_, v_k_1345_, v_cleanupAnnotations_1346_, v_whnfType_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
stack->m_obj
 = v_res_1356_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_type_1358_, lean_object* v_maxFVars_x3f_1359_, lean_object* v_k_1360_, lean_object* v_cleanupAnnotations_1361_, lean_object* v_whnfType_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1370_; uint8_t v_whnfType_boxed_1371_; lean_object* v_res_1372_; 
v_cleanupAnnotations_boxed_1370_ = lean_unbox(v_cleanupAnnotations_1361_);
v_whnfType_boxed_1371_ = lean_unbox(v_whnfType_1362_);
v_res_1372_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1357_, v_type_1358_, v_maxFVars_x3f_1359_, v_k_1360_, v_cleanupAnnotations_boxed_1370_, v_whnfType_boxed_1371_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1372_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v_toCold_1381_; lean_object* v_options_1382_; uint8_t v_hasTrace_1383_; 
v_toCold_1381_ = lean_ctor_get(v___y_1378_, 0);
v_options_1382_ = lean_ctor_get(v_toCold_1381_, 2);
v_hasTrace_1383_ = lean_ctor_get_uint8(v_options_1382_, sizeof(void*)*1);
if (v_hasTrace_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec(v_cls_1373_);
v___x_1384_ = lean_box(v_hasTrace_1383_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
else
{
lean_object* v_inheritedTraceOptions_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; uint8_t v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v_inheritedTraceOptions_1386_ = lean_ctor_get(v_toCold_1381_, 11);
v___x_1387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1388_ = l_Lean_Name_append(v___x_1387_, v_cls_1373_);
v___x_1389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1386_, v_options_1382_, v___x_1388_);
lean_dec(v___x_1388_);
v___x_1390_ = lean_box(v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1373_ = stack[0].m_obj;
lean_object* v___y_1374_ = stack[1].m_obj;
lean_object* v___y_1375_ = stack[2].m_obj;
lean_object* v___y_1376_ = stack[3].m_obj;
lean_object* v___y_1377_ = stack[4].m_obj;
lean_object* v___y_1378_ = stack[5].m_obj;
lean_object* v___y_1379_ = stack[6].m_obj;
lean_object* v_res_1392_;
v_res_1392_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
stack->m_obj
 = v_res_1392_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object* v_cls_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1401_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_mvarId_1402_, lean_object* v_val_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v___x_1406_; lean_object* v_mctx_1407_; lean_object* v_cache_1408_; lean_object* v_zetaDeltaFVarIds_1409_; lean_object* v_postponed_1410_; lean_object* v_diag_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1441_; 
v___x_1406_ = lean_st_ref_take(v___y_1404_);
v_mctx_1407_ = lean_ctor_get(v___x_1406_, 0);
v_cache_1408_ = lean_ctor_get(v___x_1406_, 1);
v_zetaDeltaFVarIds_1409_ = lean_ctor_get(v___x_1406_, 2);
v_postponed_1410_ = lean_ctor_get(v___x_1406_, 3);
v_diag_1411_ = lean_ctor_get(v___x_1406_, 4);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1413_ = v___x_1406_;
v_isShared_1414_ = v_isSharedCheck_1441_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_diag_1411_);
lean_inc(v_postponed_1410_);
lean_inc(v_zetaDeltaFVarIds_1409_);
lean_inc(v_cache_1408_);
lean_inc(v_mctx_1407_);
lean_dec(v___x_1406_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1441_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_depth_1415_; lean_object* v_levelAssignDepth_1416_; lean_object* v_lmvarCounter_1417_; lean_object* v_mvarCounter_1418_; lean_object* v_lDecls_1419_; lean_object* v_decls_1420_; lean_object* v_userNames_1421_; lean_object* v_lAssignment_1422_; lean_object* v_eAssignment_1423_; lean_object* v_dAssignment_1424_; lean_object* v_instanceTypedMVars_1425_; lean_object* v_synthNormMemo_1426_; lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1440_; 
v_depth_1415_ = lean_ctor_get(v_mctx_1407_, 0);
v_levelAssignDepth_1416_ = lean_ctor_get(v_mctx_1407_, 1);
v_lmvarCounter_1417_ = lean_ctor_get(v_mctx_1407_, 2);
v_mvarCounter_1418_ = lean_ctor_get(v_mctx_1407_, 3);
v_lDecls_1419_ = lean_ctor_get(v_mctx_1407_, 4);
v_decls_1420_ = lean_ctor_get(v_mctx_1407_, 5);
v_userNames_1421_ = lean_ctor_get(v_mctx_1407_, 6);
v_lAssignment_1422_ = lean_ctor_get(v_mctx_1407_, 7);
v_eAssignment_1423_ = lean_ctor_get(v_mctx_1407_, 8);
v_dAssignment_1424_ = lean_ctor_get(v_mctx_1407_, 9);
v_instanceTypedMVars_1425_ = lean_ctor_get(v_mctx_1407_, 10);
v_synthNormMemo_1426_ = lean_ctor_get(v_mctx_1407_, 11);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_mctx_1407_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1428_ = v_mctx_1407_;
v_isShared_1429_ = v_isSharedCheck_1440_;
goto v_resetjp_1427_;
}
else
{
lean_inc(v_synthNormMemo_1426_);
lean_inc(v_instanceTypedMVars_1425_);
lean_inc(v_dAssignment_1424_);
lean_inc(v_eAssignment_1423_);
lean_inc(v_lAssignment_1422_);
lean_inc(v_userNames_1421_);
lean_inc(v_decls_1420_);
lean_inc(v_lDecls_1419_);
lean_inc(v_mvarCounter_1418_);
lean_inc(v_lmvarCounter_1417_);
lean_inc(v_levelAssignDepth_1416_);
lean_inc(v_depth_1415_);
lean_dec(v_mctx_1407_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1440_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1433_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1423_, v_mvarId_1402_, v_val_1403_);
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 8, v___x_1431_);
v___x_1433_ = v___x_1428_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_depth_1415_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_levelAssignDepth_1416_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_lmvarCounter_1417_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v_mvarCounter_1418_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_lDecls_1419_);
lean_ctor_set(v_reuseFailAlloc_1439_, 5, v_decls_1420_);
lean_ctor_set(v_reuseFailAlloc_1439_, 6, v_userNames_1421_);
lean_ctor_set(v_reuseFailAlloc_1439_, 7, v_lAssignment_1422_);
lean_ctor_set(v_reuseFailAlloc_1439_, 8, v___x_1431_);
lean_ctor_set(v_reuseFailAlloc_1439_, 9, v_dAssignment_1424_);
lean_ctor_set(v_reuseFailAlloc_1439_, 10, v_instanceTypedMVars_1425_);
lean_ctor_set(v_reuseFailAlloc_1439_, 11, v_synthNormMemo_1426_);
v___x_1433_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
lean_object* v___x_1435_; 
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v___x_1433_);
v___x_1435_ = v___x_1413_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_cache_1408_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_zetaDeltaFVarIds_1409_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_postponed_1410_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_diag_1411_);
v___x_1435_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_st_ref_put(v___y_1404_, v___x_1435_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1430_);
return v___x_1437_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1402_ = stack[0].m_obj;
lean_object* v_val_1403_ = stack[1].m_obj;
lean_object* v___y_1404_ = stack[2].m_obj;
lean_object* v_res_1442_;
v_res_1442_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1402_, v_val_1403_, v___y_1404_);
stack->m_obj
 = v_res_1442_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_mvarId_1443_, lean_object* v_val_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1443_, v_val_1444_, v___y_1445_);
lean_dec(v___y_1445_);
return v_res_1447_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_cls_1448_, lean_object* v_msg_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v_ref_1455_; lean_object* v___x_1456_; lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1502_; 
v_ref_1455_ = lean_ctor_get(v___y_1452_, 2);
v___x_1456_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
v_a_1457_ = lean_ctor_get(v___x_1456_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1456_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1459_ = v___x_1456_;
v_isShared_1460_ = v_isSharedCheck_1502_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1456_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1502_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v_traceState_1462_; lean_object* v_env_1463_; lean_object* v_nextMacroScope_1464_; lean_object* v_ngen_1465_; lean_object* v_auxDeclNGen_1466_; lean_object* v_cache_1467_; lean_object* v_recordedDeps_1468_; lean_object* v_messages_1469_; lean_object* v_infoState_1470_; lean_object* v_snapshotTasks_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1501_; 
v___x_1461_ = lean_st_ref_take(v___y_1453_);
v_traceState_1462_ = lean_ctor_get(v___x_1461_, 4);
v_env_1463_ = lean_ctor_get(v___x_1461_, 0);
v_nextMacroScope_1464_ = lean_ctor_get(v___x_1461_, 1);
v_ngen_1465_ = lean_ctor_get(v___x_1461_, 2);
v_auxDeclNGen_1466_ = lean_ctor_get(v___x_1461_, 3);
v_cache_1467_ = lean_ctor_get(v___x_1461_, 5);
v_recordedDeps_1468_ = lean_ctor_get(v___x_1461_, 6);
v_messages_1469_ = lean_ctor_get(v___x_1461_, 7);
v_infoState_1470_ = lean_ctor_get(v___x_1461_, 8);
v_snapshotTasks_1471_ = lean_ctor_get(v___x_1461_, 9);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1473_ = v___x_1461_;
v_isShared_1474_ = v_isSharedCheck_1501_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snapshotTasks_1471_);
lean_inc(v_infoState_1470_);
lean_inc(v_messages_1469_);
lean_inc(v_recordedDeps_1468_);
lean_inc(v_cache_1467_);
lean_inc(v_traceState_1462_);
lean_inc(v_auxDeclNGen_1466_);
lean_inc(v_ngen_1465_);
lean_inc(v_nextMacroScope_1464_);
lean_inc(v_env_1463_);
lean_dec(v___x_1461_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1501_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
uint64_t v_tid_1475_; lean_object* v_traces_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1500_; 
v_tid_1475_ = lean_ctor_get_uint64(v_traceState_1462_, sizeof(void*)*1);
v_traces_1476_ = lean_ctor_get(v_traceState_1462_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_traceState_1462_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1478_ = v_traceState_1462_;
v_isShared_1479_ = v_isSharedCheck_1500_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_traces_1476_);
lean_dec(v_traceState_1462_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1500_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; double v___x_1482_; uint8_t v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_1483_ = 0;
v___x_1484_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_1485_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1485_, 0, v_cls_1448_);
lean_ctor_set(v___x_1485_, 1, v___x_1481_);
lean_ctor_set(v___x_1485_, 2, v___x_1484_);
lean_ctor_set_float(v___x_1485_, sizeof(void*)*3, v___x_1482_);
lean_ctor_set_float(v___x_1485_, sizeof(void*)*3 + 8, v___x_1482_);
lean_ctor_set_uint8(v___x_1485_, sizeof(void*)*3 + 16, v___x_1483_);
v___x_1486_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_1487_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1485_);
lean_ctor_set(v___x_1487_, 1, v_a_1457_);
lean_ctor_set(v___x_1487_, 2, v___x_1486_);
lean_inc(v_ref_1455_);
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_ref_1455_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = l_Lean_PersistentArray_push___redArg(v_traces_1476_, v___x_1488_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1489_);
v___x_1491_ = v___x_1478_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1489_);
lean_ctor_set_uint64(v_reuseFailAlloc_1499_, sizeof(void*)*1, v_tid_1475_);
v___x_1491_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v___x_1491_);
v___x_1493_ = v___x_1473_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_env_1463_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_nextMacroScope_1464_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_ngen_1465_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_auxDeclNGen_1466_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1498_, 5, v_cache_1467_);
lean_ctor_set(v_reuseFailAlloc_1498_, 6, v_recordedDeps_1468_);
lean_ctor_set(v_reuseFailAlloc_1498_, 7, v_messages_1469_);
lean_ctor_set(v_reuseFailAlloc_1498_, 8, v_infoState_1470_);
lean_ctor_set(v_reuseFailAlloc_1498_, 9, v_snapshotTasks_1471_);
v___x_1493_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_st_ref_put(v___y_1453_, v___x_1493_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1480_);
v___x_1496_ = v___x_1459_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1480_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1448_ = stack[0].m_obj;
lean_object* v_msg_1449_ = stack[1].m_obj;
lean_object* v___y_1450_ = stack[2].m_obj;
lean_object* v___y_1451_ = stack[3].m_obj;
lean_object* v___y_1452_ = stack[4].m_obj;
lean_object* v___y_1453_ = stack[5].m_obj;
lean_object* v_res_1503_;
v_res_1503_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1448_, v_msg_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
stack->m_obj
 = v_res_1503_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_cls_1504_, lean_object* v_msg_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1504_, v_msg_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
return v_res_1511_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1512_; lean_object* v_dummy_1513_; 
v___x_1512_ = lean_box(0);
v_dummy_1513_ = l_Lean_Expr_sort___override(v___x_1512_);
return v_dummy_1513_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v_numParams_1520_, lean_object* v___x_1521_, lean_object* v_name_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v_name_1525_, lean_object* v___x_1526_, lean_object* v_cls_1527_, lean_object* v_fields_1528_, lean_object* v_bodyExpr_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_toCold_1537_; lean_object* v_options_1538_; lean_object* v_inheritedTraceOptions_1539_; uint8_t v_hasTrace_1540_; lean_object* v_nargs_1541_; lean_object* v_dummy_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; 
v_toCold_1537_ = lean_ctor_get(v___y_1534_, 0);
v_options_1538_ = lean_ctor_get(v_toCold_1537_, 2);
v_inheritedTraceOptions_1539_ = lean_ctor_get(v_toCold_1537_, 11);
v_hasTrace_1540_ = lean_ctor_get_uint8(v_options_1538_, sizeof(void*)*1);
v_nargs_1541_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1529_);
v_dummy_1542_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
lean_inc(v_nargs_1541_);
v___x_1543_ = lean_mk_array(v_nargs_1541_, v_dummy_1542_);
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = lean_nat_sub(v_nargs_1541_, v___x_1544_);
lean_dec(v_nargs_1541_);
v___x_1546_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1529_, v___x_1543_, v___x_1545_);
v___x_1547_ = lean_array_get_size(v___x_1546_);
v___x_1548_ = lean_nat_add(v_numParams_1520_, v___x_1521_);
v___x_1549_ = l_Array_toSubarray___redArg(v___x_1546_, v___x_1548_, v___x_1547_);
v___x_1550_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1522_);
lean_inc(v___x_1523_);
lean_inc(v___x_1550_);
v___x_1551_ = l_Lean_mkConst(v___x_1550_, v___x_1523_);
v___x_1552_ = l_Lean_mkAppN(v___x_1551_, v___x_1524_);
v___x_1553_ = l_Subarray_copy___redArg(v___x_1549_);
v___x_1554_ = l_Lean_mkAppN(v___x_1552_, v___x_1553_);
lean_dec_ref(v___x_1553_);
if (v_hasTrace_1540_ == 0)
{
lean_dec(v_cls_1527_);
v___y_1556_ = v___y_1530_;
v___y_1557_ = v___y_1531_;
v___y_1558_ = v___y_1532_;
v___y_1559_ = v___y_1533_;
v___y_1560_ = v___y_1534_;
v___y_1561_ = v___y_1535_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
lean_inc(v_cls_1527_);
v___x_1611_ = l_Lean_Name_append(v___x_1610_, v_cls_1527_);
v___x_1612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1539_, v_options_1538_, v___x_1611_);
lean_dec(v___x_1611_);
if (v___x_1612_ == 0)
{
lean_dec(v_cls_1527_);
v___y_1556_ = v___y_1530_;
v___y_1557_ = v___y_1531_;
v___y_1558_ = v___y_1532_;
v___y_1559_ = v___y_1533_;
v___y_1560_ = v___y_1534_;
v___y_1561_ = v___y_1535_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
lean_inc(v_name_1525_);
v___x_1614_ = l_Lean_MessageData_ofName(v_name_1525_);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
lean_inc_ref(v___x_1554_);
v___x_1618_ = l_Lean_MessageData_ofExpr(v___x_1554_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1527_, v___x_1619_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref_known(v___x_1620_, 1);
v___y_1556_ = v___y_1530_;
v___y_1557_ = v___y_1531_;
v___y_1558_ = v___y_1532_;
v___y_1559_ = v___y_1533_;
v___y_1560_ = v___y_1534_;
v___y_1561_ = v___y_1535_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v___x_1554_);
lean_dec(v___x_1550_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
v___jp_1555_:
{
lean_object* v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1554_);
v___x_1563_ = 0;
v___x_1564_ = lean_box(0);
v___x_1565_ = l_Lean_Meta_mkFreshExprMVar(v___x_1562_, v___x_1563_, v___x_1564_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v_a_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_a_1566_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v___x_1565_, 1);
v___x_1567_ = l_Lean_Expr_mvarId_x21(v_a_1566_);
v___x_1568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1569_ = l_Lean_Name_append(v___x_1550_, v___x_1568_);
lean_inc(v___x_1523_);
v___x_1570_ = l_Lean_mkConst(v___x_1569_, v___x_1523_);
v___x_1571_ = l_Lean_mkAppN(v___x_1570_, v___x_1524_);
lean_inc(v___x_1567_);
v___x_1572_ = l_Lean_MVarId_getType(v___x_1567_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; uint8_t v___x_1574_; uint8_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1574_ = 0;
v___x_1575_ = 1;
v___x_1576_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1567_);
v___x_1577_ = l_Lean_MVarId_rewrite(v___x_1567_, v_a_1573_, v___x_1571_, v___x_1574_, v___x_1576_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v_eNew_1579_; lean_object* v_eqProof_1580_; lean_object* v___x_1581_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1577_, 1);
v_eNew_1579_ = lean_ctor_get(v_a_1578_, 0);
lean_inc_ref(v_eNew_1579_);
v_eqProof_1580_ = lean_ctor_get(v_a_1578_, 1);
lean_inc_ref(v_eqProof_1580_);
lean_dec(v_a_1578_);
v___x_1581_ = l_Lean_MVarId_replaceTargetEq(v___x_1567_, v_eNew_1579_, v_eqProof_1580_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_a_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v_a_1582_ = lean_ctor_get(v___x_1581_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v___x_1581_, 1);
v___x_1583_ = l_Lean_mkConst(v_name_1525_, v___x_1523_);
v___x_1584_ = l_Lean_mkAppN(v___x_1583_, v___x_1524_);
v___x_1585_ = l_Lean_mkAppN(v___x_1584_, v___x_1526_);
v___x_1586_ = l_Lean_mkAppN(v___x_1585_, v_fields_1528_);
v___x_1587_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_1582_, v___x_1586_, v___y_1559_);
lean_dec_ref(v___x_1587_);
v___x_1588_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1566_, v___y_1559_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
v___x_1590_ = 1;
v___x_1591_ = l_Lean_Meta_mkLambdaFVars(v_fields_1528_, v_a_1589_, v___x_1574_, v___x_1575_, v___x_1574_, v___x_1575_, v___x_1590_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1591_) == 0)
{
lean_object* v_a_1592_; lean_object* v___x_1593_; 
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_a_1592_);
lean_dec_ref_known(v___x_1591_, 1);
v___x_1593_ = l_Lean_Meta_mkLambdaFVars(v___x_1524_, v_a_1592_, v___x_1574_, v___x_1575_, v___x_1574_, v___x_1575_, v___x_1590_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v___x_1593_;
}
else
{
return v___x_1591_;
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
lean_dec(v_a_1566_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
v_a_1594_ = lean_ctor_get(v___x_1581_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1581_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v___x_1581_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1581_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v___x_1567_);
lean_dec(v_a_1566_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
v_a_1602_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1577_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1577_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
else
{
lean_dec_ref(v___x_1571_);
lean_dec(v___x_1567_);
lean_dec(v_a_1566_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
return v___x_1572_;
}
}
else
{
lean_dec(v___x_1550_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_1520_ = stack[0].m_obj;
lean_object* v___x_1521_ = stack[1].m_obj;
lean_object* v_name_1522_ = stack[2].m_obj;
lean_object* v___x_1523_ = stack[3].m_obj;
lean_object* v___x_1524_ = stack[4].m_obj;
lean_object* v_name_1525_ = stack[5].m_obj;
lean_object* v___x_1526_ = stack[6].m_obj;
lean_object* v_cls_1527_ = stack[7].m_obj;
lean_object* v_fields_1528_ = stack[8].m_obj;
lean_object* v_bodyExpr_1529_ = stack[9].m_obj;
lean_object* v___y_1530_ = stack[10].m_obj;
lean_object* v___y_1531_ = stack[11].m_obj;
lean_object* v___y_1532_ = stack[12].m_obj;
lean_object* v___y_1533_ = stack[13].m_obj;
lean_object* v___y_1534_ = stack[14].m_obj;
lean_object* v___y_1535_ = stack[15].m_obj;
lean_object* v_res_1629_;
v_res_1629_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1520_, v___x_1521_, v_name_1522_, v___x_1523_, v___x_1524_, v_name_1525_, v___x_1526_, v_cls_1527_, v_fields_1528_, v_bodyExpr_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
stack->m_obj
 = v_res_1629_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_1630_ = _args[0];
lean_object* v___x_1631_ = _args[1];
lean_object* v_name_1632_ = _args[2];
lean_object* v___x_1633_ = _args[3];
lean_object* v___x_1634_ = _args[4];
lean_object* v_name_1635_ = _args[5];
lean_object* v___x_1636_ = _args[6];
lean_object* v_cls_1637_ = _args[7];
lean_object* v_fields_1638_ = _args[8];
lean_object* v_bodyExpr_1639_ = _args[9];
lean_object* v___y_1640_ = _args[10];
lean_object* v___y_1641_ = _args[11];
lean_object* v___y_1642_ = _args[12];
lean_object* v___y_1643_ = _args[13];
lean_object* v___y_1644_ = _args[14];
lean_object* v___y_1645_ = _args[15];
lean_object* v___y_1646_ = _args[16];
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1630_, v___x_1631_, v_name_1632_, v___x_1633_, v___x_1634_, v_name_1635_, v___x_1636_, v_cls_1637_, v_fields_1638_, v_bodyExpr_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_fields_1638_);
lean_dec_ref(v___x_1636_);
lean_dec_ref(v___x_1634_);
lean_dec(v___x_1631_);
lean_dec(v_numParams_1630_);
return v_res_1647_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1648_, size_t v_sz_1649_, size_t v_i_1650_, lean_object* v_bs_1651_){
_start:
{
uint8_t v___x_1652_; 
v___x_1652_ = lean_usize_dec_lt(v_i_1650_, v_sz_1649_);
if (v___x_1652_ == 0)
{
return v_bs_1651_;
}
else
{
lean_object* v_v_1653_; lean_object* v___x_1654_; lean_object* v_bs_x27_1655_; lean_object* v___x_1656_; size_t v___x_1657_; size_t v___x_1658_; lean_object* v___x_1659_; 
v_v_1653_ = lean_array_uget(v_bs_1651_, v_i_1650_);
v___x_1654_ = lean_unsigned_to_nat(0u);
v_bs_x27_1655_ = lean_array_uset(v_bs_1651_, v_i_1650_, v___x_1654_);
v___x_1656_ = l_Lean_mkAppN(v_v_1653_, v___x_1648_);
v___x_1657_ = ((size_t)1ULL);
v___x_1658_ = lean_usize_add(v_i_1650_, v___x_1657_);
v___x_1659_ = lean_array_uset(v_bs_x27_1655_, v_i_1650_, v___x_1656_);
v_i_1650_ = v___x_1658_;
v_bs_1651_ = v___x_1659_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1648_ = stack[0].m_obj;
size_t v_sz_1649_ = stack[1].m_num;
size_t v_i_1650_ = stack[2].m_num;
lean_object* v_bs_1651_ = stack[3].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1648_, v_sz_1649_, v_i_1650_, v_bs_1651_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1662_, lean_object* v_sz_1663_, lean_object* v_i_1664_, lean_object* v_bs_1665_){
_start:
{
size_t v_sz_boxed_1666_; size_t v_i_boxed_1667_; lean_object* v_res_1668_; 
v_sz_boxed_1666_ = lean_unbox_usize(v_sz_1663_);
lean_dec(v_sz_1663_);
v_i_boxed_1667_ = lean_unbox_usize(v_i_1664_);
lean_dec(v_i_1664_);
v_res_1668_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1662_, v_sz_boxed_1666_, v_i_boxed_1667_, v_bs_1665_);
lean_dec_ref(v___x_1662_);
return v_res_1668_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1669_, size_t v_sz_1670_, size_t v_i_1671_, lean_object* v_bs_1672_){
_start:
{
uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1671_, v_sz_1670_);
if (v___x_1673_ == 0)
{
lean_dec(v___x_1669_);
return v_bs_1672_;
}
else
{
lean_object* v_v_1674_; lean_object* v___x_1675_; lean_object* v_bs_x27_1676_; lean_object* v___x_1677_; size_t v___x_1678_; size_t v___x_1679_; lean_object* v___x_1680_; 
v_v_1674_ = lean_array_uget(v_bs_1672_, v_i_1671_);
v___x_1675_ = lean_unsigned_to_nat(0u);
v_bs_x27_1676_ = lean_array_uset(v_bs_1672_, v_i_1671_, v___x_1675_);
lean_inc(v___x_1669_);
v___x_1677_ = l_Lean_mkConst(v_v_1674_, v___x_1669_);
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1671_, v___x_1678_);
v___x_1680_ = lean_array_uset(v_bs_x27_1676_, v_i_1671_, v___x_1677_);
v_i_1671_ = v___x_1679_;
v_bs_1672_ = v___x_1680_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1669_ = stack[0].m_obj;
size_t v_sz_1670_ = stack[1].m_num;
size_t v_i_1671_ = stack[2].m_num;
lean_object* v_bs_1672_ = stack[3].m_obj;
lean_object* v_res_1682_;
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1669_, v_sz_1670_, v_i_1671_, v_bs_1672_);
stack->m_obj
 = v_res_1682_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1683_, lean_object* v_sz_1684_, lean_object* v_i_1685_, lean_object* v_bs_1686_){
_start:
{
size_t v_sz_boxed_1687_; size_t v_i_boxed_1688_; lean_object* v_res_1689_; 
v_sz_boxed_1687_ = lean_unbox_usize(v_sz_1684_);
lean_dec(v_sz_1684_);
v_i_boxed_1688_ = lean_unbox_usize(v_i_1685_);
lean_dec(v_i_1685_);
v_res_1689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1683_, v_sz_boxed_1687_, v_i_boxed_1688_, v_bs_1686_);
return v_res_1689_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object* v___x_1693_, lean_object* v_numParams_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, size_t v___x_1697_, lean_object* v___x_1698_, lean_object* v_name_1699_, lean_object* v_name_1700_, lean_object* v_cls_1701_, lean_object* v_levelParams_1702_, lean_object* v_ctorSyntax_1703_, lean_object* v___f_1704_, lean_object* v_args_1705_, lean_object* v_body_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; size_t v_sz_1717_; lean_object* v___x_1718_; size_t v_sz_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
lean_inc_n(v_numParams_1694_, 2);
v___x_1714_ = l_Array_extract___redArg(v_args_1705_, v___x_1693_, v_numParams_1694_);
v___x_1715_ = lean_array_get_size(v_args_1705_);
v___x_1716_ = l_Array_toSubarray___redArg(v_args_1705_, v_numParams_1694_, v___x_1715_);
v_sz_1717_ = lean_array_size(v___x_1695_);
lean_inc(v___x_1696_);
v___x_1718_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1696_, v_sz_1717_, v___x_1697_, v___x_1695_);
v_sz_1719_ = lean_array_size(v___x_1718_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1714_, v_sz_1719_, v___x_1697_, v___x_1718_);
lean_inc(v_cls_1701_);
lean_inc_ref(v___x_1720_);
lean_inc(v_name_1700_);
v___f_1721_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1721_, 0, v_numParams_1694_);
lean_closure_set(v___f_1721_, 1, v___x_1698_);
lean_closure_set(v___f_1721_, 2, v_name_1699_);
lean_closure_set(v___f_1721_, 3, v___x_1696_);
lean_closure_set(v___f_1721_, 4, v___x_1714_);
lean_closure_set(v___f_1721_, 5, v_name_1700_);
lean_closure_set(v___f_1721_, 6, v___x_1720_);
lean_closure_set(v___f_1721_, 7, v_cls_1701_);
v___x_1722_ = l_Subarray_copy___redArg(v___x_1716_);
v___x_1723_ = l_Lean_Expr_replaceFVars(v_body_1706_, v___x_1722_, v___x_1720_);
lean_dec_ref(v___x_1720_);
lean_dec_ref(v___x_1722_);
v___x_1724_ = 0;
v___x_1725_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_1723_, v___f_1721_, v___x_1724_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc_n(v_a_1726_, 2);
lean_dec_ref_known(v___x_1725_, 1);
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
v___x_1727_ = lean_infer_type(v_a_1726_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___x_1752_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v___y_1708_);
lean_inc_ref(v___y_1707_);
v___x_1752_ = lean_apply_7(v___f_1704_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, lean_box(0));
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; uint8_t v___x_1754_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = lean_unbox(v_a_1753_);
lean_dec(v_a_1753_);
if (v___x_1754_ == 0)
{
lean_dec(v_cls_1701_);
v___y_1730_ = v___y_1707_;
v___y_1731_ = v___y_1708_;
v___y_1732_ = v___y_1709_;
v___y_1733_ = v___y_1710_;
v___y_1734_ = v___y_1711_;
v___y_1735_ = v___y_1712_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1755_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
lean_inc(v_a_1728_);
v___x_1756_ = l_Lean_MessageData_ofExpr(v_a_1728_);
v___x_1757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1701_, v___x_1757_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec_ref_known(v___x_1758_, 1);
v___y_1730_ = v___y_1707_;
v___y_1731_ = v___y_1708_;
v___y_1732_ = v___y_1709_;
v___y_1733_ = v___y_1710_;
v___y_1734_ = v___y_1711_;
v___y_1735_ = v___y_1712_;
goto v___jp_1729_;
}
else
{
lean_dec(v_a_1728_);
lean_dec(v_a_1726_);
lean_dec(v_ctorSyntax_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_name_1700_);
return v___x_1758_;
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_a_1728_);
lean_dec(v_a_1726_);
lean_dec(v_ctorSyntax_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_cls_1701_);
lean_dec(v_name_1700_);
v_a_1759_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1752_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1752_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
v___jp_1729_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1751_; 
v___x_1736_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1700_);
v___x_1737_ = lean_box(0);
lean_inc(v_a_1726_);
v___x_1738_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1736_, v_levelParams_1702_, v_a_1728_, v_a_1726_, v___x_1737_, v___y_1735_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1741_ = v___x_1738_;
v_isShared_1742_ = v_isSharedCheck_1751_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1738_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1751_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
lean_ctor_set_tag(v___x_1741_, 1);
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_addDecl(v___x_1744_, v___x_1724_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; lean_object* v___x_1749_; 
lean_dec_ref_known(v___x_1745_, 1);
v___x_1746_ = lean_box(0);
v___x_1747_ = lean_box(0);
v___x_1748_ = 1;
v___x_1749_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1703_, v_a_1726_, v___x_1746_, v___x_1746_, v___x_1747_, v___x_1748_, v___x_1724_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1749_;
}
else
{
lean_dec(v_a_1726_);
lean_dec(v_ctorSyntax_1703_);
return v___x_1745_;
}
}
}
}
}
else
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1774_; 
lean_dec(v_a_1726_);
lean_dec_ref(v___f_1704_);
lean_dec(v_ctorSyntax_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_cls_1701_);
lean_dec(v_name_1700_);
v_a_1767_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1769_ = v___x_1727_;
v_isShared_1770_ = v_isSharedCheck_1774_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1727_);
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
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec_ref(v___f_1704_);
lean_dec(v_ctorSyntax_1703_);
lean_dec(v_levelParams_1702_);
lean_dec(v_cls_1701_);
lean_dec(v_name_1700_);
v_a_1775_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1725_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1725_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1693_ = stack[0].m_obj;
lean_object* v_numParams_1694_ = stack[1].m_obj;
lean_object* v___x_1695_ = stack[2].m_obj;
lean_object* v___x_1696_ = stack[3].m_obj;
size_t v___x_1697_ = stack[4].m_num;
lean_object* v___x_1698_ = stack[5].m_obj;
lean_object* v_name_1699_ = stack[6].m_obj;
lean_object* v_name_1700_ = stack[7].m_obj;
lean_object* v_cls_1701_ = stack[8].m_obj;
lean_object* v_levelParams_1702_ = stack[9].m_obj;
lean_object* v_ctorSyntax_1703_ = stack[10].m_obj;
lean_object* v___f_1704_ = stack[11].m_obj;
lean_object* v_args_1705_ = stack[12].m_obj;
lean_object* v_body_1706_ = stack[13].m_obj;
lean_object* v___y_1707_ = stack[14].m_obj;
lean_object* v___y_1708_ = stack[15].m_obj;
lean_object* v___y_1709_ = stack[16].m_obj;
lean_object* v___y_1710_ = stack[17].m_obj;
lean_object* v___y_1711_ = stack[18].m_obj;
lean_object* v___y_1712_ = stack[19].m_obj;
lean_object* v_res_1783_;
v_res_1783_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1693_, v_numParams_1694_, v___x_1695_, v___x_1696_, v___x_1697_, v___x_1698_, v_name_1699_, v_name_1700_, v_cls_1701_, v_levelParams_1702_, v_ctorSyntax_1703_, v___f_1704_, v_args_1705_, v_body_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
stack->m_obj
 = v_res_1783_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object** _args){
lean_object* v___x_1784_ = _args[0];
lean_object* v_numParams_1785_ = _args[1];
lean_object* v___x_1786_ = _args[2];
lean_object* v___x_1787_ = _args[3];
lean_object* v___x_1788_ = _args[4];
lean_object* v___x_1789_ = _args[5];
lean_object* v_name_1790_ = _args[6];
lean_object* v_name_1791_ = _args[7];
lean_object* v_cls_1792_ = _args[8];
lean_object* v_levelParams_1793_ = _args[9];
lean_object* v_ctorSyntax_1794_ = _args[10];
lean_object* v___f_1795_ = _args[11];
lean_object* v_args_1796_ = _args[12];
lean_object* v_body_1797_ = _args[13];
lean_object* v___y_1798_ = _args[14];
lean_object* v___y_1799_ = _args[15];
lean_object* v___y_1800_ = _args[16];
lean_object* v___y_1801_ = _args[17];
lean_object* v___y_1802_ = _args[18];
lean_object* v___y_1803_ = _args[19];
lean_object* v___y_1804_ = _args[20];
_start:
{
size_t v___x_9303__boxed_1805_; lean_object* v_res_1806_; 
v___x_9303__boxed_1805_ = lean_unbox_usize(v___x_1788_);
lean_dec(v___x_1788_);
v_res_1806_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1784_, v_numParams_1785_, v___x_1786_, v___x_1787_, v___x_9303__boxed_1805_, v___x_1789_, v_name_1790_, v_name_1791_, v_cls_1792_, v_levelParams_1793_, v_ctorSyntax_1794_, v___f_1795_, v_args_1796_, v_body_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v___y_1801_);
lean_dec_ref(v___y_1800_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec_ref(v_body_1797_);
return v_res_1806_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1807_, size_t v_i_1808_, lean_object* v_bs_1809_){
_start:
{
uint8_t v___x_1810_; 
v___x_1810_ = lean_usize_dec_lt(v_i_1808_, v_sz_1807_);
if (v___x_1810_ == 0)
{
return v_bs_1809_;
}
else
{
lean_object* v_v_1811_; lean_object* v_toConstantVal_1812_; lean_object* v_name_1813_; lean_object* v___x_1814_; lean_object* v_bs_x27_1815_; lean_object* v___x_1816_; size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v_v_1811_ = lean_array_uget_borrowed(v_bs_1809_, v_i_1808_);
v_toConstantVal_1812_ = lean_ctor_get(v_v_1811_, 0);
v_name_1813_ = lean_ctor_get(v_toConstantVal_1812_, 0);
lean_inc(v_name_1813_);
v___x_1814_ = lean_unsigned_to_nat(0u);
v_bs_x27_1815_ = lean_array_uset(v_bs_1809_, v_i_1808_, v___x_1814_);
v___x_1816_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1813_);
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_add(v_i_1808_, v___x_1817_);
v___x_1819_ = lean_array_uset(v_bs_x27_1815_, v_i_1808_, v___x_1816_);
v_i_1808_ = v___x_1818_;
v_bs_1809_ = v___x_1819_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1807_ = stack[0].m_num;
size_t v_i_1808_ = stack[1].m_num;
lean_object* v_bs_1809_ = stack[2].m_obj;
lean_object* v_res_1821_;
v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1807_, v_i_1808_, v_bs_1809_);
stack->m_obj
 = v_res_1821_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1822_, lean_object* v_i_1823_, lean_object* v_bs_1824_){
_start:
{
size_t v_sz_boxed_1825_; size_t v_i_boxed_1826_; lean_object* v_res_1827_; 
v_sz_boxed_1825_ = lean_unbox_usize(v_sz_1822_);
lean_dec(v_sz_1822_);
v_i_boxed_1826_ = lean_unbox_usize(v_i_1823_);
lean_dec(v_i_1823_);
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1825_, v_i_boxed_1826_, v_bs_1824_);
return v_res_1827_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1831_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1));
v___x_1832_ = l_Lean_stringToMessageData(v___x_1831_);
return v___x_1832_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1835_, lean_object* v_ctorSyntax_1836_, lean_object* v_numParams_1837_, lean_object* v_name_1838_, lean_object* v_ctor_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v___x_1847_; lean_object* v_cls_1848_; lean_object* v___f_1849_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___x_1877_; lean_object* v_a_1878_; uint8_t v___x_1879_; 
v___x_1847_ = l_Lean_instInhabitedInductiveVal_default;
v_cls_1848_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___f_1849_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1877_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1848_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
if (v___x_1879_ == 0)
{
v___y_1851_ = v_a_1840_;
v___y_1852_ = v_a_1841_;
v___y_1853_ = v_a_1842_;
v___y_1854_ = v_a_1843_;
v___y_1855_ = v_a_1844_;
v___y_1856_ = v_a_1845_;
goto v___jp_1850_;
}
else
{
lean_object* v_toConstantVal_1880_; lean_object* v_name_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v_toConstantVal_1880_ = lean_ctor_get(v_ctor_1839_, 0);
v_name_1881_ = lean_ctor_get(v_toConstantVal_1880_, 0);
v___x_1882_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
lean_inc(v_name_1881_);
v___x_1883_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1881_);
v___x_1884_ = l_Lean_MessageData_ofName(v___x_1883_);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1882_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1848_, v___x_1885_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_dec_ref_known(v___x_1886_, 1);
v___y_1851_ = v_a_1840_;
v___y_1852_ = v_a_1841_;
v___y_1853_ = v_a_1842_;
v___y_1854_ = v_a_1843_;
v___y_1855_ = v_a_1844_;
v___y_1856_ = v_a_1845_;
goto v___jp_1850_;
}
else
{
lean_dec_ref(v_ctor_1839_);
lean_dec(v_name_1838_);
lean_dec(v_numParams_1837_);
lean_dec(v_ctorSyntax_1836_);
lean_dec_ref(v_infos_1835_);
return v___x_1886_;
}
}
v___jp_1850_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v_toConstantVal_1859_; lean_object* v_toConstantVal_1860_; lean_object* v_levelParams_1861_; lean_object* v_name_1862_; lean_object* v_levelParams_1863_; lean_object* v_type_1864_; lean_object* v___x_1865_; size_t v_sz_1866_; size_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___f_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1857_ = lean_unsigned_to_nat(0u);
v___x_1858_ = lean_array_get_borrowed(v___x_1847_, v_infos_1835_, v___x_1857_);
v_toConstantVal_1859_ = lean_ctor_get(v___x_1858_, 0);
v_toConstantVal_1860_ = lean_ctor_get(v_ctor_1839_, 0);
lean_inc_ref(v_toConstantVal_1860_);
lean_dec_ref(v_ctor_1839_);
v_levelParams_1861_ = lean_ctor_get(v_toConstantVal_1859_, 1);
lean_inc(v_levelParams_1861_);
v_name_1862_ = lean_ctor_get(v_toConstantVal_1860_, 0);
lean_inc(v_name_1862_);
v_levelParams_1863_ = lean_ctor_get(v_toConstantVal_1860_, 1);
lean_inc(v_levelParams_1863_);
v_type_1864_ = lean_ctor_get(v_toConstantVal_1860_, 2);
lean_inc_ref(v_type_1864_);
lean_dec_ref(v_toConstantVal_1860_);
v___x_1865_ = lean_array_get_size(v_infos_1835_);
v_sz_1866_ = lean_array_size(v_infos_1835_);
v___x_1867_ = ((size_t)0ULL);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1866_, v___x_1867_, v_infos_1835_);
v___x_1869_ = lean_box(0);
v___x_1870_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1861_, v___x_1869_);
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1837_);
v___f_1872_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed), 21, 12);
lean_closure_set(v___f_1872_, 0, v___x_1857_);
lean_closure_set(v___f_1872_, 1, v_numParams_1837_);
lean_closure_set(v___f_1872_, 2, v___x_1868_);
lean_closure_set(v___f_1872_, 3, v___x_1870_);
lean_closure_set(v___f_1872_, 4, v___x_1871_);
lean_closure_set(v___f_1872_, 5, v___x_1865_);
lean_closure_set(v___f_1872_, 6, v_name_1838_);
lean_closure_set(v___f_1872_, 7, v_name_1862_);
lean_closure_set(v___f_1872_, 8, v_cls_1848_);
lean_closure_set(v___f_1872_, 9, v_levelParams_1863_);
lean_closure_set(v___f_1872_, 10, v_ctorSyntax_1836_);
lean_closure_set(v___f_1872_, 11, v___f_1849_);
v___x_1873_ = lean_nat_add(v_numParams_1837_, v___x_1865_);
lean_dec(v_numParams_1837_);
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
v___x_1875_ = 0;
v___x_1876_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1864_, v___x_1874_, v___f_1872_, v___x_1875_, v___x_1875_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
return v___x_1876_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_1835_ = stack[0].m_obj;
lean_object* v_ctorSyntax_1836_ = stack[1].m_obj;
lean_object* v_numParams_1837_ = stack[2].m_obj;
lean_object* v_name_1838_ = stack[3].m_obj;
lean_object* v_ctor_1839_ = stack[4].m_obj;
lean_object* v_a_1840_ = stack[5].m_obj;
lean_object* v_a_1841_ = stack[6].m_obj;
lean_object* v_a_1842_ = stack[7].m_obj;
lean_object* v_a_1843_ = stack[8].m_obj;
lean_object* v_a_1844_ = stack[9].m_obj;
lean_object* v_a_1845_ = stack[10].m_obj;
lean_object* v_res_1887_;
v_res_1887_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1835_, v_ctorSyntax_1836_, v_numParams_1837_, v_name_1838_, v_ctor_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_);
stack->m_obj
 = v_res_1887_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1888_, lean_object* v_ctorSyntax_1889_, lean_object* v_numParams_1890_, lean_object* v_name_1891_, lean_object* v_ctor_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1888_, v_ctorSyntax_1889_, v_numParams_1890_, v_name_1891_, v_ctor_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
return v_res_1900_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_mvarId_1901_, lean_object* v_val_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1901_, v_val_1902_, v___y_1906_);
return v___x_1910_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1901_ = stack[0].m_obj;
lean_object* v_val_1902_ = stack[1].m_obj;
lean_object* v___y_1903_ = stack[2].m_obj;
lean_object* v___y_1904_ = stack[3].m_obj;
lean_object* v___y_1905_ = stack[4].m_obj;
lean_object* v___y_1906_ = stack[5].m_obj;
lean_object* v___y_1907_ = stack[6].m_obj;
lean_object* v___y_1908_ = stack[7].m_obj;
lean_object* v_res_1911_;
v_res_1911_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1901_, v_val_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
stack->m_obj
 = v_res_1911_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_mvarId_1912_, lean_object* v_val_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1912_, v_val_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1921_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_cls_1922_, lean_object* v_msg_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1922_, v_msg_1923_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
return v___x_1931_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1922_ = stack[0].m_obj;
lean_object* v_msg_1923_ = stack[1].m_obj;
lean_object* v___y_1924_ = stack[2].m_obj;
lean_object* v___y_1925_ = stack[3].m_obj;
lean_object* v___y_1926_ = stack[4].m_obj;
lean_object* v___y_1927_ = stack[5].m_obj;
lean_object* v___y_1928_ = stack[6].m_obj;
lean_object* v___y_1929_ = stack[7].m_obj;
lean_object* v_res_1932_;
v_res_1932_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1922_, v_msg_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
stack->m_obj
 = v_res_1932_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_cls_1933_, lean_object* v_msg_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1933_, v_msg_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
return v_res_1942_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_instMonadEIO___redArg();
return v___x_1943_;
}
}
lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v_toApplicative_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2051_; 
v___x_1958_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1959_ = l_StateRefT_x27_instMonad___redArg(v___x_1958_);
v_toApplicative_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_1959_, 1);
lean_dec(v_unused_2052_);
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_2051_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_toApplicative_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2051_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_toFunctor_1964_; lean_object* v_toSeq_1965_; lean_object* v_toSeqLeft_1966_; lean_object* v_toSeqRight_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2049_; 
v_toFunctor_1964_ = lean_ctor_get(v_toApplicative_1960_, 0);
v_toSeq_1965_ = lean_ctor_get(v_toApplicative_1960_, 2);
v_toSeqLeft_1966_ = lean_ctor_get(v_toApplicative_1960_, 3);
v_toSeqRight_1967_ = lean_ctor_get(v_toApplicative_1960_, 4);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_toApplicative_1960_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v_toApplicative_1960_, 1);
lean_dec(v_unused_2050_);
v___x_1969_ = v_toApplicative_1960_;
v_isShared_1970_ = v_isSharedCheck_2049_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_toSeqRight_1967_);
lean_inc(v_toSeqLeft_1966_);
lean_inc(v_toSeq_1965_);
lean_inc(v_toFunctor_1964_);
lean_dec(v_toApplicative_1960_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2049_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___f_1971_; lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___f_1978_; lean_object* v___x_1980_; 
v___f_1971_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1972_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1964_);
v___f_1973_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1973_, 0, v_toFunctor_1964_);
v___f_1974_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1974_, 0, v_toFunctor_1964_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___f_1973_);
lean_ctor_set(v___x_1975_, 1, v___f_1974_);
v___f_1976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1976_, 0, v_toSeqRight_1967_);
v___f_1977_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1977_, 0, v_toSeqLeft_1966_);
v___f_1978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1978_, 0, v_toSeq_1965_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 4, v___f_1976_);
lean_ctor_set(v___x_1969_, 3, v___f_1977_);
lean_ctor_set(v___x_1969_, 2, v___f_1978_);
lean_ctor_set(v___x_1969_, 1, v___f_1971_);
lean_ctor_set(v___x_1969_, 0, v___x_1975_);
v___x_1980_ = v___x_1969_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___f_1971_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v___f_1978_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v___f_1977_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v___f_1976_);
v___x_1980_ = v_reuseFailAlloc_2048_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___f_1972_);
lean_ctor_set(v___x_1962_, 0, v___x_1980_);
v___x_1982_ = v___x_1962_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___f_1972_);
v___x_1982_ = v_reuseFailAlloc_2047_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v_toApplicative_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2045_; 
v___x_1983_ = l_StateRefT_x27_instMonad___redArg(v___x_1982_);
v_toApplicative_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_1983_, 1);
lean_dec(v_unused_2046_);
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2045_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_toApplicative_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2045_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_toFunctor_1988_; lean_object* v_toSeq_1989_; lean_object* v_toSeqLeft_1990_; lean_object* v_toSeqRight_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2043_; 
v_toFunctor_1988_ = lean_ctor_get(v_toApplicative_1984_, 0);
v_toSeq_1989_ = lean_ctor_get(v_toApplicative_1984_, 2);
v_toSeqLeft_1990_ = lean_ctor_get(v_toApplicative_1984_, 3);
v_toSeqRight_1991_ = lean_ctor_get(v_toApplicative_1984_, 4);
v_isSharedCheck_2043_ = !lean_is_exclusive(v_toApplicative_1984_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v_toApplicative_1984_, 1);
lean_dec(v_unused_2044_);
v___x_1993_ = v_toApplicative_1984_;
v_isShared_1994_ = v_isSharedCheck_2043_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_toSeqRight_1991_);
lean_inc(v_toSeqLeft_1990_);
lean_inc(v_toSeq_1989_);
lean_inc(v_toFunctor_1988_);
lean_dec(v_toApplicative_1984_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2043_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___f_1995_; lean_object* v___f_1996_; lean_object* v___f_1997_; lean_object* v___f_1998_; lean_object* v___x_1999_; lean_object* v___f_2000_; lean_object* v___f_2001_; lean_object* v___f_2002_; lean_object* v___x_2004_; 
v___f_1995_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1996_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1988_);
v___f_1997_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1997_, 0, v_toFunctor_1988_);
v___f_1998_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1998_, 0, v_toFunctor_1988_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___f_1997_);
lean_ctor_set(v___x_1999_, 1, v___f_1998_);
v___f_2000_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2000_, 0, v_toSeqRight_1991_);
v___f_2001_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2001_, 0, v_toSeqLeft_1990_);
v___f_2002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2002_, 0, v_toSeq_1989_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 4, v___f_2000_);
lean_ctor_set(v___x_1993_, 3, v___f_2001_);
lean_ctor_set(v___x_1993_, 2, v___f_2002_);
lean_ctor_set(v___x_1993_, 1, v___f_1995_);
lean_ctor_set(v___x_1993_, 0, v___x_1999_);
v___x_2004_ = v___x_1993_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v___f_1995_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v___f_2002_);
lean_ctor_set(v_reuseFailAlloc_2042_, 3, v___f_2001_);
lean_ctor_set(v_reuseFailAlloc_2042_, 4, v___f_2000_);
v___x_2004_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2006_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 1, v___f_1996_);
lean_ctor_set(v___x_1986_, 0, v___x_2004_);
v___x_2006_ = v___x_1986_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2004_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___f_1996_);
v___x_2006_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v_toApplicative_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2039_; 
v___x_2007_ = l_StateRefT_x27_instMonad___redArg(v___x_2006_);
v_toApplicative_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v___x_2007_, 1);
lean_dec(v_unused_2040_);
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2039_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_toApplicative_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2039_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v_toFunctor_2012_; lean_object* v_toSeq_2013_; lean_object* v_toSeqLeft_2014_; lean_object* v_toSeqRight_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2037_; 
v_toFunctor_2012_ = lean_ctor_get(v_toApplicative_2008_, 0);
v_toSeq_2013_ = lean_ctor_get(v_toApplicative_2008_, 2);
v_toSeqLeft_2014_ = lean_ctor_get(v_toApplicative_2008_, 3);
v_toSeqRight_2015_ = lean_ctor_get(v_toApplicative_2008_, 4);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_toApplicative_2008_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v_toApplicative_2008_, 1);
lean_dec(v_unused_2038_);
v___x_2017_ = v_toApplicative_2008_;
v_isShared_2018_ = v_isSharedCheck_2037_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_toSeqRight_2015_);
lean_inc(v_toSeqLeft_2014_);
lean_inc(v_toSeq_2013_);
lean_inc(v_toFunctor_2012_);
lean_dec(v_toApplicative_2008_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2037_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___f_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___f_2022_; lean_object* v___x_2023_; lean_object* v___f_2024_; lean_object* v___f_2025_; lean_object* v___f_2026_; lean_object* v___x_2028_; 
v___f_2019_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_2020_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_2012_);
v___f_2021_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2021_, 0, v_toFunctor_2012_);
v___f_2022_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2022_, 0, v_toFunctor_2012_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___f_2021_);
lean_ctor_set(v___x_2023_, 1, v___f_2022_);
v___f_2024_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2024_, 0, v_toSeqRight_2015_);
v___f_2025_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2025_, 0, v_toSeqLeft_2014_);
v___f_2026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2026_, 0, v_toSeq_2013_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 4, v___f_2024_);
lean_ctor_set(v___x_2017_, 3, v___f_2025_);
lean_ctor_set(v___x_2017_, 2, v___f_2026_);
lean_ctor_set(v___x_2017_, 1, v___f_2019_);
lean_ctor_set(v___x_2017_, 0, v___x_2023_);
v___x_2028_ = v___x_2017_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v___f_2019_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v___f_2026_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v___f_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v___f_2024_);
v___x_2028_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___f_2020_);
lean_ctor_set(v___x_2010_, 0, v___x_2028_);
v___x_2030_ = v___x_2010_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___f_2020_);
v___x_2030_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_3785__overap_2033_; lean_object* v___x_2034_; 
v___x_2031_ = lean_box(0);
v___x_2032_ = l_instInhabitedOfMonad___redArg(v___x_2030_, v___x_2031_);
v___x_3785__overap_2033_ = lean_panic_fn_borrowed(v___x_2032_, v_msg_1950_);
lean_dec(v___x_2032_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
v___x_2034_ = lean_apply_7(v___x_3785__overap_2033_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, lean_box(0));
return v___x_2034_;
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
LEAN_EXPORT void l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1950_ = stack[0].m_obj;
lean_object* v___y_1951_ = stack[1].m_obj;
lean_object* v___y_1952_ = stack[2].m_obj;
lean_object* v___y_1953_ = stack[3].m_obj;
lean_object* v___y_1954_ = stack[4].m_obj;
lean_object* v___y_1955_ = stack[5].m_obj;
lean_object* v___y_1956_ = stack[6].m_obj;
lean_object* v_res_2053_;
v_res_2053_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
stack->m_obj
 = v_res_2053_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2062_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2063_, lean_object* v_opt_2064_){
_start:
{
lean_object* v_name_2065_; lean_object* v_defValue_2066_; lean_object* v_map_2067_; lean_object* v___x_2068_; 
v_name_2065_ = lean_ctor_get(v_opt_2064_, 0);
v_defValue_2066_ = lean_ctor_get(v_opt_2064_, 1);
v_map_2067_ = lean_ctor_get(v_opts_2063_, 0);
v___x_2068_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2067_, v_name_2065_);
if (lean_obj_tag(v___x_2068_) == 0)
{
uint8_t v___x_2069_; 
v___x_2069_ = lean_unbox(v_defValue_2066_);
return v___x_2069_;
}
else
{
lean_object* v_val_2070_; 
v_val_2070_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_val_2070_);
lean_dec_ref_known(v___x_2068_, 1);
if (lean_obj_tag(v_val_2070_) == 1)
{
uint8_t v_v_2071_; 
v_v_2071_ = lean_ctor_get_uint8(v_val_2070_, 0);
lean_dec_ref_known(v_val_2070_, 0);
return v_v_2071_;
}
else
{
uint8_t v___x_2072_; 
lean_dec(v_val_2070_);
v___x_2072_ = lean_unbox(v_defValue_2066_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_2063_ = stack[0].m_obj;
lean_object* v_opt_2064_ = stack[1].m_obj;
uint8_t v_res_2073_;
v_res_2073_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2063_, v_opt_2064_);
stack->m_num = v_res_2073_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2074_, lean_object* v_opt_2075_){
_start:
{
uint8_t v_res_2076_; lean_object* v_r_2077_; 
v_res_2076_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2074_, v_opt_2075_);
lean_dec_ref(v_opt_2075_);
lean_dec_ref(v_opts_2074_);
v_r_2077_ = lean_box(v_res_2076_);
return v_r_2077_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_box(1);
v___x_2079_ = l_Lean_MessageData_ofFormat(v___x_2078_);
return v___x_2079_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2084_ = l_Lean_MessageData_ofFormat(v___x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2085_, lean_object* v_x_2086_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
return v_x_2085_;
}
else
{
lean_object* v_head_2087_; lean_object* v_tail_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2110_; 
v_head_2087_ = lean_ctor_get(v_x_2086_, 0);
v_tail_2088_ = lean_ctor_get(v_x_2086_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_x_2086_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2090_ = v_x_2086_;
v_isShared_2091_ = v_isSharedCheck_2110_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_tail_2088_);
lean_inc(v_head_2087_);
lean_dec(v_x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2110_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_before_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2108_; 
v_before_2092_ = lean_ctor_get(v_head_2087_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_head_2087_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v_head_2087_, 1);
lean_dec(v_unused_2109_);
v___x_2094_ = v_head_2087_;
v_isShared_2095_ = v_isSharedCheck_2108_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_before_2092_);
lean_dec(v_head_2087_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2108_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set_tag(v___x_2094_, 7);
lean_ctor_set(v___x_2094_, 1, v___x_2096_);
lean_ctor_set(v___x_2094_, 0, v_x_2085_);
v___x_2098_ = v___x_2094_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_x_2085_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2091_ == 0)
{
lean_ctor_set_tag(v___x_2090_, 7);
lean_ctor_set(v___x_2090_, 1, v___x_2099_);
lean_ctor_set(v___x_2090_, 0, v___x_2098_);
v___x_2101_ = v___x_2090_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = l_Lean_MessageData_ofSyntax(v_before_2092_);
v___x_2103_ = l_Lean_indentD(v___x_2102_);
v___x_2104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2101_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v_x_2085_ = v___x_2104_;
v_x_2086_ = v_tail_2088_;
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
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2115_ = l_Lean_MessageData_ofFormat(v___x_2114_);
return v___x_2115_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2116_, lean_object* v_macroStack_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v___x_2120_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2118_);
v___x_2121_ = l_Lean_Elab_pp_macroStack;
v___x_2122_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v___x_2120_, v___x_2121_);
lean_dec_ref(v___x_2120_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_dec(v_macroStack_2117_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_msgData_2116_);
return v___x_2123_;
}
else
{
if (lean_obj_tag(v_macroStack_2117_) == 0)
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_msgData_2116_);
return v___x_2124_;
}
else
{
lean_object* v_head_2125_; lean_object* v_after_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2141_; 
v_head_2125_ = lean_ctor_get(v_macroStack_2117_, 0);
lean_inc(v_head_2125_);
v_after_2126_ = lean_ctor_get(v_head_2125_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_head_2125_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; 
v_unused_2142_ = lean_ctor_get(v_head_2125_, 0);
lean_dec(v_unused_2142_);
v___x_2128_ = v_head_2125_;
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_after_2126_);
lean_dec(v_head_2125_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2141_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2130_; lean_object* v___x_2132_; 
v___x_2130_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2129_ == 0)
{
lean_ctor_set_tag(v___x_2128_, 7);
lean_ctor_set(v___x_2128_, 1, v___x_2130_);
lean_ctor_set(v___x_2128_, 0, v_msgData_2116_);
v___x_2132_ = v___x_2128_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_msgData_2116_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2130_);
v___x_2132_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v_msgData_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2133_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_MessageData_ofSyntax(v_after_2126_);
v___x_2136_ = l_Lean_indentD(v___x_2135_);
v_msgData_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2137_, 0, v___x_2134_);
lean_ctor_set(v_msgData_2137_, 1, v___x_2136_);
v___x_2138_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2137_, v_macroStack_2117_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2116_ = stack[0].m_obj;
lean_object* v_macroStack_2117_ = stack[1].m_obj;
lean_object* v___y_2118_ = stack[2].m_obj;
lean_object* v_res_2143_;
v_res_2143_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2116_, v_macroStack_2117_, v___y_2118_);
stack->m_obj
 = v_res_2143_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2144_, lean_object* v_macroStack_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2144_, v_macroStack_2145_, v___y_2146_);
lean_dec_ref(v___y_2146_);
return v_res_2148_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v_ref_2157_; lean_object* v_macroStack_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_a_2161_; lean_object* v___x_2162_; lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2171_; 
v_ref_2157_ = lean_ctor_get(v___y_2154_, 2);
v_macroStack_2158_ = lean_ctor_get(v___y_2150_, 1);
v___x_2159_ = l_Lean_Elab_getBetterRef(v_ref_2157_, v_macroStack_2158_);
v___x_2160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2149_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2160_);
lean_inc(v_macroStack_2158_);
v___x_2162_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2161_, v_macroStack_2158_, v___y_2154_);
v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2165_ = v___x_2162_;
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2162_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2171_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2159_);
lean_ctor_set(v___x_2167_, 1, v_a_2163_);
if (v_isShared_2166_ == 0)
{
lean_ctor_set_tag(v___x_2165_, 1);
lean_ctor_set(v___x_2165_, 0, v___x_2167_);
v___x_2169_ = v___x_2165_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2149_ = stack[0].m_obj;
lean_object* v___y_2150_ = stack[1].m_obj;
lean_object* v___y_2151_ = stack[2].m_obj;
lean_object* v___y_2152_ = stack[3].m_obj;
lean_object* v___y_2153_ = stack[4].m_obj;
lean_object* v___y_2154_ = stack[5].m_obj;
lean_object* v___y_2155_ = stack[6].m_obj;
lean_object* v_res_2172_;
v_res_2172_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
stack->m_obj
 = v_res_2172_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v_res_2181_; 
v_res_2181_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2181_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2184_ = l_Lean_stringToMessageData(v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2187_ = l_Lean_stringToMessageData(v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2191_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2192_ = lean_unsigned_to_nat(11u);
v___x_2193_ = lean_unsigned_to_nat(122u);
v___x_2194_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2195_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2196_ = l_mkPanicMessageWithDecl(v___x_2195_, v___x_2194_, v___x_2193_, v___x_2192_, v___x_2191_);
return v___x_2196_;
}
}
lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2213_; lean_object* v_env_2214_; uint8_t v___x_2215_; lean_object* v___x_2216_; 
v___x_2213_ = lean_st_ref_get(v___y_2203_);
v_env_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc_ref(v_env_2214_);
lean_dec(v___x_2213_);
v___x_2215_ = 0;
lean_inc(v_constName_2197_);
v___x_2216_ = l_Lean_Environment_findAsync_x3f(v_env_2214_, v_constName_2197_, v___x_2215_);
if (lean_obj_tag(v___x_2216_) == 1)
{
lean_object* v_val_2217_; uint8_t v_kind_2218_; 
v_val_2217_ = lean_ctor_get(v___x_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v___x_2216_, 1);
v_kind_2218_ = lean_ctor_get_uint8(v_val_2217_, sizeof(void*)*3);
if (v_kind_2218_ == 6)
{
lean_object* v___x_2219_; 
v___x_2219_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2217_);
if (lean_obj_tag(v___x_2219_) == 6)
{
lean_object* v_val_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_constName_2197_);
v_val_2220_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2219_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_val_2220_);
lean_dec(v___x_2219_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
lean_ctor_set_tag(v___x_2222_, 0);
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_val_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
else
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v___x_2219_);
v___x_2228_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2229_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2228_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2238_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2238_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
if (lean_obj_tag(v_a_2230_) == 0)
{
lean_del_object(v___x_2232_);
goto v___jp_2205_;
}
else
{
lean_object* v_val_2234_; lean_object* v___x_2236_; 
lean_dec(v_constName_2197_);
v_val_2234_ = lean_ctor_get(v_a_2230_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v_a_2230_, 1);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v_val_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_val_2234_);
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
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_constName_2197_);
v_a_2239_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2229_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2229_);
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
}
else
{
lean_dec(v_val_2217_);
goto v___jp_2205_;
}
}
else
{
lean_dec(v___x_2216_);
goto v___jp_2205_;
}
v___jp_2205_:
{
lean_object* v___x_2206_; uint8_t v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2206_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2207_ = 0;
v___x_2208_ = l_Lean_MessageData_ofConstName(v_constName_2197_, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2206_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2211_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2212_;
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2197_ = stack[0].m_obj;
lean_object* v___y_2198_ = stack[1].m_obj;
lean_object* v___y_2199_ = stack[2].m_obj;
lean_object* v___y_2200_ = stack[3].m_obj;
lean_object* v___y_2201_ = stack[4].m_obj;
lean_object* v___y_2202_ = stack[5].m_obj;
lean_object* v___y_2203_ = stack[6].m_obj;
lean_object* v_res_2247_;
v_res_2247_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
stack->m_obj
 = v_res_2247_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
return v_res_2256_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2257_, lean_object* v_infos_2258_, lean_object* v_numParams_2259_, lean_object* v_as_x27_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
if (lean_obj_tag(v_as_x27_2260_) == 0)
{
lean_object* v___x_2269_; 
lean_dec(v_numParams_2259_);
lean_dec_ref(v_infos_2258_);
lean_dec_ref(v_a_2257_);
v___x_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_b_2261_);
return v___x_2269_;
}
else
{
lean_object* v_head_2270_; lean_object* v_tail_2271_; lean_object* v_array_2272_; lean_object* v_start_2273_; lean_object* v_stop_2274_; uint8_t v___x_2275_; 
v_head_2270_ = lean_ctor_get(v_as_x27_2260_, 0);
v_tail_2271_ = lean_ctor_get(v_as_x27_2260_, 1);
v_array_2272_ = lean_ctor_get(v_b_2261_, 0);
v_start_2273_ = lean_ctor_get(v_b_2261_, 1);
v_stop_2274_ = lean_ctor_get(v_b_2261_, 2);
v___x_2275_ = lean_nat_dec_lt(v_start_2273_, v_stop_2274_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2276_; 
lean_dec(v_numParams_2259_);
lean_dec_ref(v_infos_2258_);
lean_dec_ref(v_a_2257_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_b_2261_);
return v___x_2276_;
}
else
{
lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2308_; 
lean_inc(v_stop_2274_);
lean_inc(v_start_2273_);
lean_inc_ref(v_array_2272_);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_b_2261_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; lean_object* v_unused_2310_; lean_object* v_unused_2311_; 
v_unused_2309_ = lean_ctor_get(v_b_2261_, 2);
lean_dec(v_unused_2309_);
v_unused_2310_ = lean_ctor_get(v_b_2261_, 1);
lean_dec(v_unused_2310_);
v_unused_2311_ = lean_ctor_get(v_b_2261_, 0);
lean_dec(v_unused_2311_);
v___x_2278_ = v_b_2261_;
v_isShared_2279_ = v_isSharedCheck_2308_;
goto v_resetjp_2277_;
}
else
{
lean_dec(v_b_2261_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2308_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2280_ = lean_array_fget(v_array_2272_, v_start_2273_);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_nat_add(v_start_2273_, v___x_2281_);
lean_dec(v_start_2273_);
if (v_isShared_2279_ == 0)
{
lean_ctor_set(v___x_2278_, 1, v___x_2282_);
v___x_2284_ = v___x_2278_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_array_2272_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_stop_2274_);
v___x_2284_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; 
lean_inc(v_head_2270_);
v___x_2285_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2270_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_toConstantVal_2286_; lean_object* v_a_2287_; lean_object* v_name_2288_; lean_object* v___x_2289_; 
v_toConstantVal_2286_ = lean_ctor_get(v_a_2257_, 0);
v_a_2287_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2285_, 1);
v_name_2288_ = lean_ctor_get(v_toConstantVal_2286_, 0);
lean_inc(v_name_2288_);
lean_inc(v_numParams_2259_);
lean_inc_ref(v_infos_2258_);
v___x_2289_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2258_, v___x_2280_, v_numParams_2259_, v_name_2288_, v_a_2287_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_dec_ref_known(v___x_2289_, 1);
v_as_x27_2260_ = v_tail_2271_;
v_b_2261_ = v___x_2284_;
goto _start;
}
else
{
lean_object* v_a_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2298_; 
lean_dec_ref(v___x_2284_);
lean_dec(v_numParams_2259_);
lean_dec_ref(v_infos_2258_);
lean_dec_ref(v_a_2257_);
v_a_2291_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2293_ = v___x_2289_;
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_a_2291_);
lean_dec(v___x_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2298_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2296_; 
if (v_isShared_2294_ == 0)
{
v___x_2296_ = v___x_2293_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec_ref(v___x_2284_);
lean_dec(v___x_2280_);
lean_dec(v_numParams_2259_);
lean_dec_ref(v_infos_2258_);
lean_dec_ref(v_a_2257_);
v_a_2299_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2285_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2285_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2257_ = stack[0].m_obj;
lean_object* v_infos_2258_ = stack[1].m_obj;
lean_object* v_numParams_2259_ = stack[2].m_obj;
lean_object* v_as_x27_2260_ = stack[3].m_obj;
lean_object* v_b_2261_ = stack[4].m_obj;
lean_object* v___y_2262_ = stack[5].m_obj;
lean_object* v___y_2263_ = stack[6].m_obj;
lean_object* v___y_2264_ = stack[7].m_obj;
lean_object* v___y_2265_ = stack[8].m_obj;
lean_object* v___y_2266_ = stack[9].m_obj;
lean_object* v___y_2267_ = stack[10].m_obj;
lean_object* v_res_2312_;
v_res_2312_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2257_, v_infos_2258_, v_numParams_2259_, v_as_x27_2260_, v_b_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
stack->m_obj
 = v_res_2312_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2313_, lean_object* v_infos_2314_, lean_object* v_numParams_2315_, lean_object* v_as_x27_2316_, lean_object* v_b_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2313_, v_infos_2314_, v_numParams_2315_, v_as_x27_2316_, v_b_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v_as_x27_2316_);
return v_res_2325_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2326_, lean_object* v_numParams_2327_, lean_object* v_as_2328_, size_t v_sz_2329_, size_t v_i_2330_, lean_object* v_b_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
uint8_t v___x_2339_; 
v___x_2339_ = lean_usize_dec_lt(v_i_2330_, v_sz_2329_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
lean_dec(v_numParams_2327_);
lean_dec_ref(v_infos_2326_);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v_b_2331_);
return v___x_2340_;
}
else
{
lean_object* v_array_2341_; lean_object* v_start_2342_; lean_object* v_stop_2343_; uint8_t v___x_2344_; 
v_array_2341_ = lean_ctor_get(v_b_2331_, 0);
v_start_2342_ = lean_ctor_get(v_b_2331_, 1);
v_stop_2343_ = lean_ctor_get(v_b_2331_, 2);
v___x_2344_ = lean_nat_dec_lt(v_start_2342_, v_stop_2343_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2345_; 
lean_dec(v_numParams_2327_);
lean_dec_ref(v_infos_2326_);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v_b_2331_);
return v___x_2345_;
}
else
{
lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2373_; 
lean_inc(v_stop_2343_);
lean_inc(v_start_2342_);
lean_inc_ref(v_array_2341_);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_b_2331_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; lean_object* v_unused_2375_; lean_object* v_unused_2376_; 
v_unused_2374_ = lean_ctor_get(v_b_2331_, 2);
lean_dec(v_unused_2374_);
v_unused_2375_ = lean_ctor_get(v_b_2331_, 1);
lean_dec(v_unused_2375_);
v_unused_2376_ = lean_ctor_get(v_b_2331_, 0);
lean_dec(v_unused_2376_);
v___x_2347_ = v_b_2331_;
v_isShared_2348_ = v_isSharedCheck_2373_;
goto v_resetjp_2346_;
}
else
{
lean_dec(v_b_2331_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2373_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v_ctorSyntax_2350_; lean_object* v_a_2351_; lean_object* v_ctors_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2349_ = lean_array_fget_borrowed(v_array_2341_, v_start_2342_);
v_ctorSyntax_2350_ = lean_ctor_get(v___x_2349_, 4);
lean_inc_ref(v_ctorSyntax_2350_);
v_a_2351_ = lean_array_uget_borrowed(v_as_2328_, v_i_2330_);
v_ctors_2352_ = lean_ctor_get(v_a_2351_, 4);
v___x_2353_ = lean_array_get_size(v_ctorSyntax_2350_);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v_start_2342_, v___x_2354_);
lean_dec(v_start_2342_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set(v___x_2347_, 1, v___x_2355_);
v___x_2357_ = v___x_2347_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_array_2341_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_stop_2343_);
v___x_2357_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_unsigned_to_nat(0u);
v___x_2359_ = l_Array_toSubarray___redArg(v_ctorSyntax_2350_, v___x_2358_, v___x_2353_);
lean_inc(v_numParams_2327_);
lean_inc_ref(v_infos_2326_);
lean_inc(v_a_2351_);
v___x_2360_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2351_, v_infos_2326_, v_numParams_2327_, v_ctors_2352_, v___x_2359_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2360_) == 0)
{
size_t v___x_2361_; size_t v___x_2362_; 
lean_dec_ref_known(v___x_2360_, 1);
v___x_2361_ = ((size_t)1ULL);
v___x_2362_ = lean_usize_add(v_i_2330_, v___x_2361_);
v_i_2330_ = v___x_2362_;
v_b_2331_ = v___x_2357_;
goto _start;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec_ref(v___x_2357_);
lean_dec(v_numParams_2327_);
lean_dec_ref(v_infos_2326_);
v_a_2364_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2360_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2360_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_2326_ = stack[0].m_obj;
lean_object* v_numParams_2327_ = stack[1].m_obj;
lean_object* v_as_2328_ = stack[2].m_obj;
size_t v_sz_2329_ = stack[3].m_num;
size_t v_i_2330_ = stack[4].m_num;
lean_object* v_b_2331_ = stack[5].m_obj;
lean_object* v___y_2332_ = stack[6].m_obj;
lean_object* v___y_2333_ = stack[7].m_obj;
lean_object* v___y_2334_ = stack[8].m_obj;
lean_object* v___y_2335_ = stack[9].m_obj;
lean_object* v___y_2336_ = stack[10].m_obj;
lean_object* v___y_2337_ = stack[11].m_obj;
lean_object* v_res_2377_;
v_res_2377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2326_, v_numParams_2327_, v_as_2328_, v_sz_2329_, v_i_2330_, v_b_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
stack->m_obj
 = v_res_2377_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2378_, lean_object* v_numParams_2379_, lean_object* v_as_2380_, lean_object* v_sz_2381_, lean_object* v_i_2382_, lean_object* v_b_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
size_t v_sz_boxed_2391_; size_t v_i_boxed_2392_; lean_object* v_res_2393_; 
v_sz_boxed_2391_ = lean_unbox_usize(v_sz_2381_);
lean_dec(v_sz_2381_);
v_i_boxed_2392_ = lean_unbox_usize(v_i_2382_);
lean_dec(v_i_2382_);
v_res_2393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2378_, v_numParams_2379_, v_as_2380_, v_sz_boxed_2391_, v_i_boxed_2392_, v_b_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec_ref(v_as_2380_);
return v_res_2393_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2394_, lean_object* v_infos_2395_, lean_object* v_coinductiveElabData_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; size_t v_sz_2407_; size_t v___x_2408_; lean_object* v___x_2409_; 
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_array_get_size(v_coinductiveElabData_2396_);
v___x_2406_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2396_, v___x_2404_, v___x_2405_);
v_sz_2407_ = lean_array_size(v_infos_2395_);
v___x_2408_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2395_);
v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2395_, v_numParams_2394_, v_infos_2395_, v_sz_2407_, v___x_2408_, v___x_2406_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec_ref(v_infos_2395_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2417_; 
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v___x_2409_, 0);
lean_dec(v_unused_2418_);
v___x_2411_ = v___x_2409_;
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
else
{
lean_dec(v___x_2409_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2417_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2413_; lean_object* v___x_2415_; 
v___x_2413_ = lean_box(0);
if (v_isShared_2412_ == 0)
{
lean_ctor_set(v___x_2411_, 0, v___x_2413_);
v___x_2415_ = v___x_2411_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
return v___x_2415_;
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2409_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2409_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_2394_ = stack[0].m_obj;
lean_object* v_infos_2395_ = stack[1].m_obj;
lean_object* v_coinductiveElabData_2396_ = stack[2].m_obj;
lean_object* v_a_2397_ = stack[3].m_obj;
lean_object* v_a_2398_ = stack[4].m_obj;
lean_object* v_a_2399_ = stack[5].m_obj;
lean_object* v_a_2400_ = stack[6].m_obj;
lean_object* v_a_2401_ = stack[7].m_obj;
lean_object* v_a_2402_ = stack[8].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2394_, v_infos_2395_, v_coinductiveElabData_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
stack->m_obj
 = v_res_2427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2428_, lean_object* v_infos_2429_, lean_object* v_coinductiveElabData_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2428_, v_infos_2429_, v_coinductiveElabData_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
return v_res_2438_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2439_, lean_object* v_infos_2440_, lean_object* v_numParams_2441_, lean_object* v_as_2442_, lean_object* v_as_x27_2443_, lean_object* v_b_2444_, lean_object* v_a_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2439_, v_infos_2440_, v_numParams_2441_, v_as_x27_2443_, v_b_2444_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2439_ = stack[0].m_obj;
lean_object* v_infos_2440_ = stack[1].m_obj;
lean_object* v_numParams_2441_ = stack[2].m_obj;
lean_object* v_as_2442_ = stack[3].m_obj;
lean_object* v_as_x27_2443_ = stack[4].m_obj;
lean_object* v_b_2444_ = stack[5].m_obj;
lean_object* v___y_2446_ = stack[7].m_obj;
lean_object* v___y_2447_ = stack[8].m_obj;
lean_object* v___y_2448_ = stack[9].m_obj;
lean_object* v___y_2449_ = stack[10].m_obj;
lean_object* v___y_2450_ = stack[11].m_obj;
lean_object* v___y_2451_ = stack[12].m_obj;
lean_object* v_res_2454_;
v_res_2454_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2439_, v_infos_2440_, v_numParams_2441_, v_as_2442_, v_as_x27_2443_, v_b_2444_, lean_box(0), v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
stack->m_obj
 = v_res_2454_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2455_, lean_object* v_infos_2456_, lean_object* v_numParams_2457_, lean_object* v_as_2458_, lean_object* v_as_x27_2459_, lean_object* v_b_2460_, lean_object* v_a_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2455_, v_infos_2456_, v_numParams_2457_, v_as_2458_, v_as_x27_2459_, v_b_2460_, v_a_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v_as_x27_2459_);
lean_dec(v_as_2458_);
return v_res_2469_;
}
}
lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2470_, lean_object* v_msg_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
lean_object* v___x_2479_; 
v___x_2479_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
return v___x_2479_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2471_ = stack[1].m_obj;
lean_object* v___y_2472_ = stack[2].m_obj;
lean_object* v___y_2473_ = stack[3].m_obj;
lean_object* v___y_2474_ = stack[4].m_obj;
lean_object* v___y_2475_ = stack[5].m_obj;
lean_object* v___y_2476_ = stack[6].m_obj;
lean_object* v___y_2477_ = stack[7].m_obj;
lean_object* v_res_2480_;
v_res_2480_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_box(0), v_msg_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
stack->m_obj
 = v_res_2480_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2481_, lean_object* v_msg_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2481_, v_msg_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2490_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2491_, lean_object* v_macroStack_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2491_, v_macroStack_2492_, v___y_2497_);
return v___x_2500_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2491_ = stack[0].m_obj;
lean_object* v_macroStack_2492_ = stack[1].m_obj;
lean_object* v___y_2493_ = stack[2].m_obj;
lean_object* v___y_2494_ = stack[3].m_obj;
lean_object* v___y_2495_ = stack[4].m_obj;
lean_object* v___y_2496_ = stack[5].m_obj;
lean_object* v___y_2497_ = stack[6].m_obj;
lean_object* v___y_2498_ = stack[7].m_obj;
lean_object* v_res_2501_;
v_res_2501_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2491_, v_macroStack_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
stack->m_obj
 = v_res_2501_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2502_, lean_object* v_macroStack_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2502_, v_macroStack_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2511_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_mvarId_2512_, lean_object* v_x_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2512_, v_x_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
if (lean_obj_tag(v___x_2519_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_a_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_a_2528_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2519_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2519_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2512_ = stack[0].m_obj;
lean_object* v_x_2513_ = stack[1].m_obj;
lean_object* v___y_2514_ = stack[2].m_obj;
lean_object* v___y_2515_ = stack[3].m_obj;
lean_object* v___y_2516_ = stack[4].m_obj;
lean_object* v___y_2517_ = stack[5].m_obj;
lean_object* v_res_2536_;
v_res_2536_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2512_, v_x_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
stack->m_obj
 = v_res_2536_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_mvarId_2537_, lean_object* v_x_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2537_, v_x_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
return v_res_2544_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2545_, lean_object* v_mvarId_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2546_, v_x_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2546_ = stack[1].m_obj;
lean_object* v_x_2547_ = stack[2].m_obj;
lean_object* v___y_2548_ = stack[3].m_obj;
lean_object* v___y_2549_ = stack[4].m_obj;
lean_object* v___y_2550_ = stack[5].m_obj;
lean_object* v___y_2551_ = stack[6].m_obj;
lean_object* v_res_2554_;
v_res_2554_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_box(0), v_mvarId_2546_, v_x_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
stack->m_obj
 = v_res_2554_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2555_, lean_object* v_mvarId_2556_, lean_object* v_x_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2555_, v_mvarId_2556_, v_x_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
return v_res_2563_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_type_2564_, lean_object* v_maxFVars_x3f_2565_, lean_object* v_k_2566_, uint8_t v_cleanupAnnotations_2567_, uint8_t v_whnfType_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___f_2574_; lean_object* v___x_2575_; 
v___f_2574_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2574_, 0, v_k_2566_);
v___x_2575_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2564_, v_maxFVars_x3f_2565_, v___f_2574_, v_cleanupAnnotations_2567_, v_whnfType_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2575_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2575_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
v_a_2584_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2575_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2575_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2564_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_2565_ = stack[1].m_obj;
lean_object* v_k_2566_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2567_ = stack[3].m_num;
uint8_t v_whnfType_2568_ = stack[4].m_num;
lean_object* v___y_2569_ = stack[5].m_obj;
lean_object* v___y_2570_ = stack[6].m_obj;
lean_object* v___y_2571_ = stack[7].m_obj;
lean_object* v___y_2572_ = stack[8].m_obj;
lean_object* v_res_2592_;
v_res_2592_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2564_, v_maxFVars_x3f_2565_, v_k_2566_, v_cleanupAnnotations_2567_, v_whnfType_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
stack->m_obj
 = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_type_2593_, lean_object* v_maxFVars_x3f_2594_, lean_object* v_k_2595_, lean_object* v_cleanupAnnotations_2596_, lean_object* v_whnfType_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2603_; uint8_t v_whnfType_boxed_2604_; lean_object* v_res_2605_; 
v_cleanupAnnotations_boxed_2603_ = lean_unbox(v_cleanupAnnotations_2596_);
v_whnfType_boxed_2604_ = lean_unbox(v_whnfType_2597_);
v_res_2605_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2593_, v_maxFVars_x3f_2594_, v_k_2595_, v_cleanupAnnotations_boxed_2603_, v_whnfType_boxed_2604_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2605_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2606_, lean_object* v_type_2607_, lean_object* v_maxFVars_x3f_2608_, lean_object* v_k_2609_, uint8_t v_cleanupAnnotations_2610_, uint8_t v_whnfType_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v___x_2617_; 
v___x_2617_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2607_, v_maxFVars_x3f_2608_, v_k_2609_, v_cleanupAnnotations_2610_, v_whnfType_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
return v___x_2617_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_2607_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_2608_ = stack[2].m_obj;
lean_object* v_k_2609_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_2610_ = stack[4].m_num;
uint8_t v_whnfType_2611_ = stack[5].m_num;
lean_object* v___y_2612_ = stack[6].m_obj;
lean_object* v___y_2613_ = stack[7].m_obj;
lean_object* v___y_2614_ = stack[8].m_obj;
lean_object* v___y_2615_ = stack[9].m_obj;
lean_object* v_res_2618_;
v_res_2618_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_box(0), v_type_2607_, v_maxFVars_x3f_2608_, v_k_2609_, v_cleanupAnnotations_2610_, v_whnfType_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_);
stack->m_obj
 = v_res_2618_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2619_, lean_object* v_type_2620_, lean_object* v_maxFVars_x3f_2621_, lean_object* v_k_2622_, lean_object* v_cleanupAnnotations_2623_, lean_object* v_whnfType_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2630_; uint8_t v_whnfType_boxed_2631_; lean_object* v_res_2632_; 
v_cleanupAnnotations_boxed_2630_ = lean_unbox(v_cleanupAnnotations_2623_);
v_whnfType_boxed_2631_ = lean_unbox(v_whnfType_2624_);
v_res_2632_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2619_, v_type_2620_, v_maxFVars_x3f_2621_, v_k_2622_, v_cleanupAnnotations_boxed_2630_, v_whnfType_boxed_2631_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2632_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2633_, lean_object* v_msg_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_toCold_2640_; lean_object* v_currRecDepth_2641_; lean_object* v_ref_2642_; uint16_t v_optionFlags_2643_; uint8_t v_suppressElabErrors_2644_; uint8_t v_isRecordingDeps_2645_; lean_object* v_ref_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_toCold_2640_ = lean_ctor_get(v___y_2637_, 0);
v_currRecDepth_2641_ = lean_ctor_get(v___y_2637_, 1);
v_ref_2642_ = lean_ctor_get(v___y_2637_, 2);
v_optionFlags_2643_ = lean_ctor_get_uint16(v___y_2637_, sizeof(void*)*3);
v_suppressElabErrors_2644_ = lean_ctor_get_uint8(v___y_2637_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2645_ = lean_ctor_get_uint8(v___y_2637_, sizeof(void*)*3 + 3);
v_ref_2646_ = l_Lean_replaceRef(v_ref_2633_, v_ref_2642_);
lean_inc(v_currRecDepth_2641_);
lean_inc_ref(v_toCold_2640_);
v___x_2647_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2647_, 0, v_toCold_2640_);
lean_ctor_set(v___x_2647_, 1, v_currRecDepth_2641_);
lean_ctor_set(v___x_2647_, 2, v_ref_2646_);
lean_ctor_set_uint16(v___x_2647_, sizeof(void*)*3, v_optionFlags_2643_);
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*3 + 2, v_suppressElabErrors_2644_);
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*3 + 3, v_isRecordingDeps_2645_);
v___x_2648_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2634_, v___y_2635_, v___y_2636_, v___x_2647_, v___y_2638_);
lean_dec_ref_known(v___x_2647_, 3);
return v___x_2648_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2633_ = stack[0].m_obj;
lean_object* v_msg_2634_ = stack[1].m_obj;
lean_object* v___y_2635_ = stack[2].m_obj;
lean_object* v___y_2636_ = stack[3].m_obj;
lean_object* v___y_2637_ = stack[4].m_obj;
lean_object* v___y_2638_ = stack[5].m_obj;
lean_object* v_res_2649_;
v_res_2649_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2633_, v_msg_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
stack->m_obj
 = v_res_2649_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2650_, lean_object* v_msg_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2650_, v_msg_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v_ref_2650_);
return v_res_2657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2662_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2663_ = lean_unsigned_to_nat(0u);
v___x_2664_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
lean_ctor_set(v___x_2664_, 2, v___x_2663_);
lean_ctor_set(v___x_2664_, 3, v___x_2663_);
lean_ctor_set(v___x_2664_, 4, v___x_2662_);
lean_ctor_set(v___x_2664_, 5, v___x_2662_);
lean_ctor_set(v___x_2664_, 6, v___x_2662_);
lean_ctor_set(v___x_2664_, 7, v___x_2662_);
lean_ctor_set(v___x_2664_, 8, v___x_2662_);
lean_ctor_set(v___x_2664_, 9, v___x_2662_);
lean_ctor_set(v___x_2664_, 10, v___x_2662_);
lean_ctor_set(v___x_2664_, 11, v___x_2661_);
return v___x_2664_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2665_ = lean_unsigned_to_nat(32u);
v___x_2666_ = lean_mk_empty_array_with_capacity(v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
return v___x_2667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v___x_2668_ = ((size_t)5ULL);
v___x_2669_ = lean_unsigned_to_nat(0u);
v___x_2670_ = lean_unsigned_to_nat(32u);
v___x_2671_ = lean_mk_empty_array_with_capacity(v___x_2670_);
v___x_2672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2673_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2673_, 0, v___x_2672_);
lean_ctor_set(v___x_2673_, 1, v___x_2671_);
lean_ctor_set(v___x_2673_, 2, v___x_2669_);
lean_ctor_set(v___x_2673_, 3, v___x_2669_);
lean_ctor_set_usize(v___x_2673_, 4, v___x_2668_);
return v___x_2673_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2674_ = lean_box(1);
v___x_2675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
lean_ctor_set(v___x_2677_, 1, v___x_2675_);
lean_ctor_set(v___x_2677_, 2, v___x_2674_);
return v___x_2677_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2680_ = l_Lean_stringToMessageData(v___x_2679_);
return v___x_2680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2683_ = l_Lean_stringToMessageData(v___x_2682_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2685_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2686_ = l_Lean_stringToMessageData(v___x_2685_);
return v___x_2686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2689_ = l_Lean_stringToMessageData(v___x_2688_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2691_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2692_ = l_Lean_stringToMessageData(v___x_2691_);
return v___x_2692_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2695_ = l_Lean_stringToMessageData(v___x_2694_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2698_ = l_Lean_stringToMessageData(v___x_2697_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__21(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__20));
v___x_2701_ = l_Lean_stringToMessageData(v___x_2700_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__23(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__22));
v___x_2704_ = l_Lean_stringToMessageData(v___x_2703_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__25(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2706_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__24));
v___x_2707_ = l_Lean_stringToMessageData(v___x_2706_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__27(void){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__26));
v___x_2710_ = l_Lean_stringToMessageData(v___x_2709_);
return v___x_2710_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2711_, lean_object* v_declHint_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v_env_2717_; uint8_t v___x_2718_; 
v___x_2715_ = lean_box(0);
v___x_2716_ = lean_st_ref_get(v___y_2713_);
v_env_2717_ = lean_ctor_get(v___x_2716_, 0);
lean_inc_ref(v_env_2717_);
lean_dec(v___x_2716_);
v___x_2718_ = l_Lean_Name_isAnonymous(v_declHint_2712_);
if (v___x_2718_ == 0)
{
uint8_t v_isExporting_2719_; 
v_isExporting_2719_ = lean_ctor_get_uint8(v_env_2717_, sizeof(void*)*13);
if (v_isExporting_2719_ == 0)
{
lean_object* v___x_2720_; 
lean_dec_ref(v_env_2717_);
lean_dec(v_declHint_2712_);
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_msg_2711_);
return v___x_2720_;
}
else
{
lean_object* v___x_2721_; uint8_t v___x_2722_; 
lean_inc_ref(v_env_2717_);
v___x_2721_ = l_Lean_Environment_setExporting(v_env_2717_, v___x_2718_);
lean_inc(v_declHint_2712_);
lean_inc_ref(v___x_2721_);
v___x_2722_ = l_Lean_Environment_contains(v___x_2721_, v_declHint_2712_, v_isExporting_2719_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
lean_dec_ref(v___x_2721_);
lean_dec_ref(v_env_2717_);
lean_dec(v_declHint_2712_);
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v_msg_2711_);
return v___x_2723_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v_c_2729_; lean_object* v___x_2730_; 
v___x_2724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2725_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2726_ = l_Lean_Options_empty;
v___x_2727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2721_);
lean_ctor_set(v___x_2727_, 1, v___x_2724_);
lean_ctor_set(v___x_2727_, 2, v___x_2725_);
lean_ctor_set(v___x_2727_, 3, v___x_2726_);
lean_inc(v_declHint_2712_);
v___x_2728_ = l_Lean_MessageData_ofConstName(v_declHint_2712_, v___x_2718_);
v_c_2729_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2729_, 0, v___x_2727_);
lean_ctor_set(v_c_2729_, 1, v___x_2728_);
v___x_2730_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2717_, v_declHint_2712_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec_ref(v_env_2717_);
lean_dec(v_declHint_2712_);
v___x_2731_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2732_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v_c_2729_);
v___x_2733_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2732_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = l_Lean_MessageData_note(v___x_2734_);
v___x_2736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_msg_2711_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2736_);
return v___x_2737_;
}
else
{
lean_object* v_val_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2794_; 
v_val_2738_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2740_ = v___x_2730_;
v_isShared_2741_ = v_isSharedCheck_2794_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_val_2738_);
lean_dec(v___x_2730_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2794_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2742_; lean_object* v_modules_2743_; lean_object* v_moduleNames_2744_; lean_object* v_mod_2745_; uint8_t v___y_2747_; uint8_t v___x_2777_; 
v___x_2742_ = l_Lean_Environment_header(v_env_2717_);
lean_dec_ref(v_env_2717_);
v_modules_2743_ = lean_ctor_get(v___x_2742_, 3);
lean_inc_ref(v_modules_2743_);
v_moduleNames_2744_ = lean_ctor_get(v___x_2742_, 4);
lean_inc_ref(v_moduleNames_2744_);
lean_dec_ref(v___x_2742_);
v_mod_2745_ = lean_array_get(v___x_2715_, v_moduleNames_2744_, v_val_2738_);
lean_dec_ref(v_moduleNames_2744_);
v___x_2777_ = l_Lean_isPrivateName(v_declHint_2712_);
lean_dec(v_declHint_2712_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2778_ = lean_array_get_size(v_modules_2743_);
v___x_2779_ = lean_nat_dec_lt(v_val_2738_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_dec_ref(v_modules_2743_);
lean_dec(v_val_2738_);
v___y_2747_ = v___x_2777_;
goto v___jp_2746_;
}
else
{
lean_object* v___x_2780_; lean_object* v_toImport_2781_; uint8_t v_isExported_2782_; 
v___x_2780_ = lean_array_fget(v_modules_2743_, v_val_2738_);
lean_dec(v_val_2738_);
lean_dec_ref(v_modules_2743_);
v_toImport_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc_ref(v_toImport_2781_);
lean_dec(v___x_2780_);
v_isExported_2782_ = lean_ctor_get_uint8(v_toImport_2781_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_2781_);
v___y_2747_ = v_isExported_2782_;
goto v___jp_2746_;
}
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
lean_dec_ref(v_modules_2743_);
lean_del_object(v___x_2740_);
lean_dec(v_val_2738_);
v___x_2783_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set(v___x_2784_, 1, v_c_2729_);
v___x_2785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__25);
v___x_2786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = l_Lean_MessageData_ofName(v_mod_2745_);
v___x_2788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__27);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2788_);
lean_ctor_set(v___x_2790_, 1, v___x_2789_);
v___x_2791_ = l_Lean_MessageData_note(v___x_2790_);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_msg_2711_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
return v___x_2793_;
}
v___jp_2746_:
{
if (v___y_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v_c_2729_);
v___x_2750_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
v___x_2752_ = l_Lean_MessageData_ofName(v_mod_2745_);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2753_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = l_Lean_MessageData_note(v___x_2755_);
v___x_2757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_msg_2711_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2757_);
v___x_2759_ = v___x_2740_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v_c_2729_);
v___x_2763_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2762_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = l_Lean_MessageData_ofName(v_mod_2745_);
lean_inc_ref(v___x_2765_);
v___x_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2764_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__21);
v___x_2768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
lean_ctor_set(v___x_2769_, 1, v___x_2765_);
v___x_2770_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__23);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_MessageData_note(v___x_2771_);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v_msg_2711_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set_tag(v___x_2740_, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2773_);
v___x_2775_ = v___x_2740_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
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
lean_object* v___x_2795_; 
lean_dec_ref(v_env_2717_);
lean_dec(v_declHint_2712_);
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_msg_2711_);
return v___x_2795_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2711_ = stack[0].m_obj;
lean_object* v_declHint_2712_ = stack[1].m_obj;
lean_object* v___y_2713_ = stack[2].m_obj;
lean_object* v_res_2796_;
v_res_2796_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2711_, v_declHint_2712_, v___y_2713_);
stack->m_obj
 = v_res_2796_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2797_, lean_object* v_declHint_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2797_, v_declHint_2798_, v___y_2799_);
lean_dec(v___y_2799_);
return v_res_2801_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2802_, lean_object* v_declHint_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2819_; 
v___x_2809_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2802_, v_declHint_2803_, v___y_2807_);
v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2812_ = v___x_2809_;
v_isShared_2813_ = v_isSharedCheck_2819_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2809_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2819_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2814_ = l_Lean_unknownIdentifierMessageTag;
v___x_2815_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_a_2810_);
if (v_isShared_2813_ == 0)
{
lean_ctor_set(v___x_2812_, 0, v___x_2815_);
v___x_2817_ = v___x_2812_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2802_ = stack[0].m_obj;
lean_object* v_declHint_2803_ = stack[1].m_obj;
lean_object* v___y_2804_ = stack[2].m_obj;
lean_object* v___y_2805_ = stack[3].m_obj;
lean_object* v___y_2806_ = stack[4].m_obj;
lean_object* v___y_2807_ = stack[5].m_obj;
lean_object* v_res_2820_;
v_res_2820_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2802_, v_declHint_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
stack->m_obj
 = v_res_2820_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2821_, lean_object* v_declHint_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2821_, v_declHint_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
return v_res_2828_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2829_, lean_object* v_msg_2830_, lean_object* v_declHint_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v___x_2837_; lean_object* v_a_2838_; lean_object* v___x_2839_; 
v___x_2837_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2830_, v_declHint_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref(v___x_2837_);
v___x_2839_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2829_, v_a_2838_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
return v___x_2839_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2829_ = stack[0].m_obj;
lean_object* v_msg_2830_ = stack[1].m_obj;
lean_object* v_declHint_2831_ = stack[2].m_obj;
lean_object* v___y_2832_ = stack[3].m_obj;
lean_object* v___y_2833_ = stack[4].m_obj;
lean_object* v___y_2834_ = stack[5].m_obj;
lean_object* v___y_2835_ = stack[6].m_obj;
lean_object* v_res_2840_;
v_res_2840_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2829_, v_msg_2830_, v_declHint_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
stack->m_obj
 = v_res_2840_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2841_, lean_object* v_msg_2842_, lean_object* v_declHint_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2841_, v_msg_2842_, v_declHint_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_ref_2841_);
return v_res_2849_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2852_ = l_Lean_stringToMessageData(v___x_2851_);
return v___x_2852_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2853_, lean_object* v_constName_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v___x_2860_; uint8_t v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2860_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2861_ = 0;
lean_inc(v_constName_2854_);
v___x_2862_ = l_Lean_MessageData_ofConstName(v_constName_2854_, v___x_2861_);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2860_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2863_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2853_, v___x_2865_, v_constName_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
return v___x_2866_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2853_ = stack[0].m_obj;
lean_object* v_constName_2854_ = stack[1].m_obj;
lean_object* v___y_2855_ = stack[2].m_obj;
lean_object* v___y_2856_ = stack[3].m_obj;
lean_object* v___y_2857_ = stack[4].m_obj;
lean_object* v___y_2858_ = stack[5].m_obj;
lean_object* v_res_2867_;
v_res_2867_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2853_, v_constName_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
stack->m_obj
 = v_res_2867_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2868_, lean_object* v_constName_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2868_, v_constName_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v_ref_2868_);
return v_res_2875_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_ref_2882_; lean_object* v___x_2883_; 
v_ref_2882_ = lean_ctor_get(v___y_2879_, 2);
v___x_2883_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2882_, v_constName_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
return v___x_2883_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2876_ = stack[0].m_obj;
lean_object* v___y_2877_ = stack[1].m_obj;
lean_object* v___y_2878_ = stack[2].m_obj;
lean_object* v___y_2879_ = stack[3].m_obj;
lean_object* v___y_2880_ = stack[4].m_obj;
lean_object* v_res_2884_;
v_res_2884_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
stack->m_obj
 = v_res_2884_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2891_;
}
}
lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v_env_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; 
v___x_2898_ = lean_st_ref_get(v___y_2896_);
v_env_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_env_2899_);
lean_dec(v___x_2898_);
v___x_2900_ = 0;
lean_inc(v_constName_2892_);
v___x_2901_ = l_Lean_Environment_find_x3f(v_env_2899_, v_constName_2892_, v___x_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v___x_2902_; 
v___x_2902_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
return v___x_2902_;
}
else
{
lean_object* v_val_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_constName_2892_);
v_val_2903_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2901_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_val_2903_);
lean_dec(v___x_2901_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 0);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_val_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2892_ = stack[0].m_obj;
lean_object* v___y_2893_ = stack[1].m_obj;
lean_object* v___y_2894_ = stack[2].m_obj;
lean_object* v___y_2895_ = stack[3].m_obj;
lean_object* v___y_2896_ = stack[4].m_obj;
lean_object* v_res_2911_;
v_res_2911_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
stack->m_obj
 = v_res_2911_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
return v_res_2918_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2919_, lean_object* v_as_2920_, size_t v_i_2921_, size_t v_stop_2922_){
_start:
{
uint8_t v___x_2923_; 
v___x_2923_ = lean_usize_dec_eq(v_i_2921_, v_stop_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2924_ = lean_array_uget_borrowed(v_as_2920_, v_i_2921_);
v___x_2925_ = l_Lean_Expr_isAppOf(v_e_2919_, v___x_2924_);
if (v___x_2925_ == 0)
{
size_t v___x_2926_; size_t v___x_2927_; 
v___x_2926_ = ((size_t)1ULL);
v___x_2927_ = lean_usize_add(v_i_2921_, v___x_2926_);
v_i_2921_ = v___x_2927_;
goto _start;
}
else
{
return v___x_2925_;
}
}
else
{
uint8_t v___x_2929_; 
v___x_2929_ = 0;
return v___x_2929_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2919_ = stack[0].m_obj;
lean_object* v_as_2920_ = stack[1].m_obj;
size_t v_i_2921_ = stack[2].m_num;
size_t v_stop_2922_ = stack[3].m_num;
uint8_t v_res_2930_;
v_res_2930_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2919_, v_as_2920_, v_i_2921_, v_stop_2922_);
stack->m_num = v_res_2930_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2931_, lean_object* v_as_2932_, lean_object* v_i_2933_, lean_object* v_stop_2934_){
_start:
{
size_t v_i_boxed_2935_; size_t v_stop_boxed_2936_; uint8_t v_res_2937_; lean_object* v_r_2938_; 
v_i_boxed_2935_ = lean_unbox_usize(v_i_2933_);
lean_dec(v_i_2933_);
v_stop_boxed_2936_ = lean_unbox_usize(v_stop_2934_);
lean_dec(v_stop_2934_);
v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2931_, v_as_2932_, v_i_boxed_2935_, v_stop_boxed_2936_);
lean_dec_ref(v_as_2932_);
lean_dec_ref(v_e_2931_);
v_r_2938_ = lean_box(v_res_2937_);
return v_r_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2939_, lean_object* v_name_2940_, lean_object* v___y_2941_, lean_object* v___x_2942_, lean_object* v_levels_2943_, lean_object* v_params_2944_, lean_object* v_e_2945_){
_start:
{
uint8_t v___x_2946_; 
v___x_2946_ = l_Lean_Expr_isApp(v_e_2945_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; 
lean_dec_ref(v_e_2945_);
lean_dec_ref(v_params_2944_);
lean_dec(v_levels_2943_);
lean_dec(v_name_2940_);
lean_dec(v_numParams_2939_);
v___x_2947_ = lean_box(0);
return v___x_2947_;
}
else
{
lean_object* v_dummy_2948_; lean_object* v_nargs_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; uint8_t v___x_2956_; 
v_dummy_2948_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2949_ = l_Lean_Expr_getAppNumArgs(v_e_2945_);
lean_inc(v_nargs_2949_);
v___x_2950_ = lean_mk_array(v_nargs_2949_, v_dummy_2948_);
v___x_2951_ = lean_unsigned_to_nat(1u);
v___x_2952_ = lean_nat_sub(v_nargs_2949_, v___x_2951_);
lean_dec(v_nargs_2949_);
lean_inc_ref(v_e_2945_);
v___x_2953_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2945_, v___x_2950_, v___x_2952_);
v___x_2954_ = lean_array_get_size(v___x_2953_);
v___x_2955_ = l_Array_toSubarray___redArg(v___x_2953_, v_numParams_2939_, v___x_2954_);
v___x_2956_ = l_Lean_Expr_isAppOf(v_e_2945_, v_name_2940_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; uint8_t v___x_2958_; 
lean_dec(v_name_2940_);
v___x_2957_ = lean_array_get_size(v___y_2941_);
v___x_2958_ = lean_nat_dec_lt(v___x_2942_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; 
lean_dec_ref(v___x_2955_);
lean_dec_ref(v_e_2945_);
lean_dec_ref(v_params_2944_);
lean_dec(v_levels_2943_);
v___x_2959_ = lean_box(0);
return v___x_2959_;
}
else
{
if (v___x_2958_ == 0)
{
lean_object* v___x_2960_; 
lean_dec_ref(v___x_2955_);
lean_dec_ref(v_e_2945_);
lean_dec_ref(v_params_2944_);
lean_dec(v_levels_2943_);
v___x_2960_ = lean_box(0);
return v___x_2960_;
}
else
{
size_t v___x_2961_; size_t v___x_2962_; uint8_t v___x_2963_; 
v___x_2961_ = ((size_t)0ULL);
v___x_2962_ = lean_usize_of_nat(v___x_2957_);
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2945_, v___y_2941_, v___x_2961_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; 
lean_dec_ref(v___x_2955_);
lean_dec_ref(v_e_2945_);
lean_dec_ref(v_params_2944_);
lean_dec(v_levels_2943_);
v___x_2964_ = lean_box(0);
return v___x_2964_;
}
else
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2965_ = l_Lean_Expr_getAppFn(v_e_2945_);
lean_dec_ref(v_e_2945_);
v___x_2966_ = l_Lean_Expr_constName(v___x_2965_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2966_);
v___x_2968_ = l_Lean_mkConst(v___x_2967_, v_levels_2943_);
v___x_2969_ = l_Subarray_copy___redArg(v___x_2955_);
v___x_2970_ = l_Array_append___redArg(v_params_2944_, v___x_2969_);
lean_dec_ref(v___x_2969_);
v___x_2971_ = l_Lean_mkAppN(v___x_2968_, v___x_2970_);
lean_dec_ref(v___x_2970_);
v___x_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
}
}
else
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref(v_e_2945_);
v___x_2973_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2940_);
v___x_2974_ = l_Lean_mkConst(v___x_2973_, v_levels_2943_);
v___x_2975_ = l_Subarray_copy___redArg(v___x_2955_);
v___x_2976_ = l_Array_append___redArg(v_params_2944_, v___x_2975_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = l_Lean_mkAppN(v___x_2974_, v___x_2976_);
lean_dec_ref(v___x_2976_);
v___x_2978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2979_, lean_object* v_name_2980_, lean_object* v___y_2981_, lean_object* v___x_2982_, lean_object* v_levels_2983_, lean_object* v_params_2984_, lean_object* v_e_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2979_, v_name_2980_, v___y_2981_, v___x_2982_, v_levels_2983_, v_params_2984_, v_e_2985_);
lean_dec(v___x_2982_);
lean_dec_ref(v___y_2981_);
return v_res_2986_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v_eqProof_2987_, lean_object* v___x_2988_, lean_object* v_eNew_2989_, lean_object* v_snd_2990_, lean_object* v___x_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Lean_Meta_mkEqMP(v_eqProof_2987_, v___x_2988_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_eNew_2989_);
v___x_3000_ = lean_box(0);
v___x_3001_ = l_Lean_MVarId_replace(v_snd_2990_, v___x_2991_, v_a_2998_, v___x_2999_, v___x_3000_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
return v___x_3001_;
}
else
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3009_; 
lean_dec(v___x_2991_);
lean_dec(v_snd_2990_);
lean_dec_ref(v_eNew_2989_);
v_a_3002_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3004_ = v___x_2997_;
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_2997_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3009_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v___x_3007_; 
if (v_isShared_3005_ == 0)
{
v___x_3007_ = v___x_3004_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_a_3002_);
v___x_3007_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
return v___x_3007_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_eqProof_2987_ = stack[0].m_obj;
lean_object* v___x_2988_ = stack[1].m_obj;
lean_object* v_eNew_2989_ = stack[2].m_obj;
lean_object* v_snd_2990_ = stack[3].m_obj;
lean_object* v___x_2991_ = stack[4].m_obj;
lean_object* v___y_2992_ = stack[5].m_obj;
lean_object* v___y_2993_ = stack[6].m_obj;
lean_object* v___y_2994_ = stack[7].m_obj;
lean_object* v___y_2995_ = stack[8].m_obj;
lean_object* v_res_3010_;
v_res_3010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_2987_, v___x_2988_, v_eNew_2989_, v_snd_2990_, v___x_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
stack->m_obj
 = v_res_3010_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object* v_eqProof_3011_, lean_object* v___x_3012_, lean_object* v_eNew_3013_, lean_object* v_snd_3014_, lean_object* v___x_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_3011_, v___x_3012_, v_eNew_3013_, v_snd_3014_, v___x_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
return v_res_3021_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0));
v___x_3024_ = l_Lean_stringToMessageData(v___x_3023_);
return v___x_3024_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_3048_, lean_object* v___x_3049_, lean_object* v___x_3050_, uint8_t v___x_3051_, lean_object* v___x_3052_, lean_object* v___x_3053_, uint8_t v___x_3054_, lean_object* v_params_3055_, lean_object* v_args_3056_, lean_object* v_indices_3057_, uint8_t v___x_3058_, lean_object* v_a_3059_, lean_object* v___x_3060_, lean_object* v___x_3061_, lean_object* v___f_3062_, lean_object* v___x_3063_, lean_object* v_targetArgs_3064_, lean_object* v_x_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v___x_3071_; uint8_t v___x_3072_; 
v___x_3071_ = lean_array_get_size(v_targetArgs_3064_);
v___x_3072_ = lean_nat_dec_eq(v___x_3071_, v___x_3048_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
lean_dec_ref(v___x_3053_);
lean_dec(v___x_3052_);
lean_dec_ref(v___x_3050_);
v___x_3073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3074_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3073_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
return v___x_3074_;
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3075_ = lean_array_fget_borrowed(v_targetArgs_3064_, v___x_3049_);
lean_inc(v___y_3069_);
lean_inc_ref(v___y_3068_);
lean_inc(v___y_3067_);
lean_inc_ref(v___y_3066_);
lean_inc_ref(v___x_3050_);
v___x_3076_ = lean_infer_type(v___x_3050_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
if (lean_obj_tag(v_a_3077_) == 7)
{
lean_object* v_binderType_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_binderType_3078_ = lean_ctor_get(v_a_3077_, 1);
lean_inc_ref(v_binderType_3078_);
lean_dec_ref_known(v_a_3077_, 3);
v___x_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3079_, 0, v_binderType_3078_);
v___x_3080_ = l_Lean_Meta_mkFreshExprMVar(v___x_3079_, v___x_3051_, v___x_3052_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_Expr_mvarId_x21(v_a_3081_);
v___x_3083_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_3082_, v___x_3053_, v___x_3054_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
lean_inc(v___x_3075_);
v___x_3085_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_3084_, v___x_3075_, v___y_3067_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3167_; 
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v___x_3085_, 0);
lean_dec(v_unused_3168_);
v___x_3087_ = v___x_3085_;
v_isShared_3088_ = v_isSharedCheck_3167_;
goto v_resetjp_3086_;
}
else
{
lean_dec(v___x_3085_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3167_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; 
v___x_3089_ = l_Lean_Expr_app___override(v___x_3050_, v_a_3081_);
lean_inc_ref(v_params_3055_);
v___x_3090_ = l_Array_append___redArg(v_params_3055_, v_args_3056_);
v___x_3091_ = l_Array_append___redArg(v___x_3090_, v_indices_3057_);
v___x_3092_ = l_Array_append___redArg(v___x_3091_, v_targetArgs_3064_);
v___x_3093_ = 1;
v___x_3094_ = l_Lean_Meta_mkLambdaFVars(v___x_3092_, v___x_3089_, v___x_3058_, v___x_3054_, v___x_3058_, v___x_3054_, v___x_3093_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec_ref(v___x_3092_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3096_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3096_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_3095_, v___y_3067_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc(v_a_3097_);
lean_dec_ref_known(v___x_3096_, 1);
v___x_3098_ = l_Lean_ConstantInfo_levelParams(v_a_3059_);
v___x_3099_ = l_Lean_mkCasesOnName(v___x_3060_);
v___x_3100_ = l_Lean_Meta_mkForallFVars(v_params_3055_, v___x_3061_, v___x_3058_, v___x_3054_, v___x_3054_, v___x_3093_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
lean_dec_ref(v_params_3055_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = lean_box(0);
lean_inc(v___x_3099_);
v___x_3103_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_3099_, v___x_3098_, v_a_3101_, v_a_3097_, v___x_3102_, v___y_3069_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3106_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 1);
lean_ctor_set(v___x_3087_, 0, v_a_3104_);
v___x_3106_ = v___x_3087_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3104_);
v___x_3106_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3107_; 
v___x_3107_ = l_Lean_addDecl(v___x_3106_, v___x_3058_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
lean_dec_ref_known(v___x_3107_, 1);
v___x_3108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8));
v___x_3109_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3109_, 0, v___x_3099_);
lean_closure_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_box(0);
v___x_3112_ = lean_box(1);
v___x_3113_ = lean_mk_empty_array_with_capacity(v___x_3049_);
v___x_3114_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3114_, 0, v___x_3110_);
lean_ctor_set(v___x_3114_, 1, v___x_3111_);
lean_ctor_set(v___x_3114_, 2, v___x_3110_);
lean_ctor_set(v___x_3114_, 3, v___f_3062_);
lean_ctor_set(v___x_3114_, 4, v___x_3112_);
lean_ctor_set(v___x_3114_, 5, v___x_3112_);
lean_ctor_set(v___x_3114_, 6, v___x_3110_);
lean_ctor_set(v___x_3114_, 7, v___x_3113_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8, v___x_3054_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 1, v___x_3054_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 2, v___x_3054_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 3, v___x_3054_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 4, v___x_3058_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 5, v___x_3058_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 6, v___x_3058_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 7, v___x_3058_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 8, v___x_3054_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 9, v___x_3058_);
lean_ctor_set_uint8(v___x_3114_, sizeof(void*)*8 + 10, v___x_3054_);
v___x_3115_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3063_);
lean_ctor_set(v___x_3115_, 1, v___x_3112_);
lean_ctor_set(v___x_3115_, 2, v___x_3111_);
lean_ctor_set(v___x_3115_, 3, v___x_3111_);
lean_ctor_set(v___x_3115_, 4, v___x_3111_);
lean_ctor_set(v___x_3115_, 5, v___x_3112_);
lean_ctor_set(v___x_3115_, 6, v___x_3111_);
v___x_3116_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3109_, v___x_3114_, v___x_3115_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3125_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3125_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v_fst_3121_; lean_object* v___x_3123_; 
v_fst_3121_ = lean_ctor_get(v_a_3117_, 0);
lean_inc(v_fst_3121_);
lean_dec(v_a_3117_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v_fst_3121_);
v___x_3123_ = v___x_3119_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_fst_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
v_a_3126_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3116_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3116_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_dec(v___x_3099_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
return v___x_3107_;
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v___x_3099_);
lean_del_object(v___x_3087_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
v_a_3135_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3103_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3103_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
lean_dec(v___x_3099_);
lean_dec(v___x_3098_);
lean_dec(v_a_3097_);
lean_del_object(v___x_3087_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
v_a_3143_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3100_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3100_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_del_object(v___x_3087_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
v_a_3151_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3096_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3096_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
else
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
lean_del_object(v___x_3087_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
v_a_3159_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___x_3094_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___x_3094_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
else
{
lean_dec(v_a_3081_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
lean_dec_ref(v___x_3050_);
return v___x_3085_;
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_a_3081_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
lean_dec_ref(v___x_3050_);
v_a_3169_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3083_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3083_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
lean_dec_ref(v___x_3053_);
lean_dec_ref(v___x_3050_);
v_a_3177_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3080_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3080_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v_a_3077_);
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
lean_dec_ref(v___x_3053_);
lean_dec(v___x_3052_);
lean_dec_ref(v___x_3050_);
v___x_3185_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3186_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3185_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
return v___x_3186_;
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v___x_3063_);
lean_dec_ref(v___f_3062_);
lean_dec_ref(v___x_3061_);
lean_dec(v___x_3060_);
lean_dec_ref(v_params_3055_);
lean_dec_ref(v___x_3053_);
lean_dec(v___x_3052_);
lean_dec_ref(v___x_3050_);
v_a_3187_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3076_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3076_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3048_ = stack[0].m_obj;
lean_object* v___x_3049_ = stack[1].m_obj;
lean_object* v___x_3050_ = stack[2].m_obj;
uint8_t v___x_3051_ = stack[3].m_num;
lean_object* v___x_3052_ = stack[4].m_obj;
lean_object* v___x_3053_ = stack[5].m_obj;
uint8_t v___x_3054_ = stack[6].m_num;
lean_object* v_params_3055_ = stack[7].m_obj;
lean_object* v_args_3056_ = stack[8].m_obj;
lean_object* v_indices_3057_ = stack[9].m_obj;
uint8_t v___x_3058_ = stack[10].m_num;
lean_object* v_a_3059_ = stack[11].m_obj;
lean_object* v___x_3060_ = stack[12].m_obj;
lean_object* v___x_3061_ = stack[13].m_obj;
lean_object* v___f_3062_ = stack[14].m_obj;
lean_object* v___x_3063_ = stack[15].m_obj;
lean_object* v_targetArgs_3064_ = stack[16].m_obj;
lean_object* v_x_3065_ = stack[17].m_obj;
lean_object* v___y_3066_ = stack[18].m_obj;
lean_object* v___y_3067_ = stack[19].m_obj;
lean_object* v___y_3068_ = stack[20].m_obj;
lean_object* v___y_3069_ = stack[21].m_obj;
lean_object* v_res_3195_;
v_res_3195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3048_, v___x_3049_, v___x_3050_, v___x_3051_, v___x_3052_, v___x_3053_, v___x_3054_, v_params_3055_, v_args_3056_, v_indices_3057_, v___x_3058_, v_a_3059_, v___x_3060_, v___x_3061_, v___f_3062_, v___x_3063_, v_targetArgs_3064_, v_x_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_);
stack->m_obj
 = v_res_3195_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3196_ = _args[0];
lean_object* v___x_3197_ = _args[1];
lean_object* v___x_3198_ = _args[2];
lean_object* v___x_3199_ = _args[3];
lean_object* v___x_3200_ = _args[4];
lean_object* v___x_3201_ = _args[5];
lean_object* v___x_3202_ = _args[6];
lean_object* v_params_3203_ = _args[7];
lean_object* v_args_3204_ = _args[8];
lean_object* v_indices_3205_ = _args[9];
lean_object* v___x_3206_ = _args[10];
lean_object* v_a_3207_ = _args[11];
lean_object* v___x_3208_ = _args[12];
lean_object* v___x_3209_ = _args[13];
lean_object* v___f_3210_ = _args[14];
lean_object* v___x_3211_ = _args[15];
lean_object* v_targetArgs_3212_ = _args[16];
lean_object* v_x_3213_ = _args[17];
lean_object* v___y_3214_ = _args[18];
lean_object* v___y_3215_ = _args[19];
lean_object* v___y_3216_ = _args[20];
lean_object* v___y_3217_ = _args[21];
lean_object* v___y_3218_ = _args[22];
_start:
{
uint8_t v___x_16872__boxed_3219_; uint8_t v___x_16875__boxed_3220_; uint8_t v___x_16876__boxed_3221_; lean_object* v_res_3222_; 
v___x_16872__boxed_3219_ = lean_unbox(v___x_3199_);
v___x_16875__boxed_3220_ = lean_unbox(v___x_3202_);
v___x_16876__boxed_3221_ = lean_unbox(v___x_3206_);
v_res_3222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3196_, v___x_3197_, v___x_3198_, v___x_16872__boxed_3219_, v___x_3200_, v___x_3201_, v___x_16875__boxed_3220_, v_params_3203_, v_args_3204_, v_indices_3205_, v___x_16876__boxed_3221_, v_a_3207_, v___x_3208_, v___x_3209_, v___f_3210_, v___x_3211_, v_targetArgs_3212_, v_x_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec_ref(v_x_3213_);
lean_dec_ref(v_targetArgs_3212_);
lean_dec_ref(v_a_3207_);
lean_dec_ref(v_indices_3205_);
lean_dec_ref(v_args_3204_);
lean_dec(v___x_3197_);
lean_dec(v___x_3196_);
return v_res_3222_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v___x_3225_, uint8_t v___x_3226_, lean_object* v___x_3227_, lean_object* v___x_3228_, uint8_t v___x_3229_, lean_object* v_params_3230_, lean_object* v_args_3231_, uint8_t v___x_3232_, lean_object* v_a_3233_, lean_object* v___x_3234_, lean_object* v___x_3235_, lean_object* v___f_3236_, lean_object* v___x_3237_, lean_object* v___x_3238_, lean_object* v_indices_3239_, lean_object* v_goalType_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___f_3250_; lean_object* v___x_3251_; 
v___x_3246_ = l_Lean_mkAppN(v___x_3223_, v_indices_3239_);
v___x_3247_ = lean_box(v___x_3226_);
v___x_3248_ = lean_box(v___x_3229_);
v___x_3249_ = lean_box(v___x_3232_);
v___f_3250_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 23, 16);
lean_closure_set(v___f_3250_, 0, v___x_3224_);
lean_closure_set(v___f_3250_, 1, v___x_3225_);
lean_closure_set(v___f_3250_, 2, v___x_3246_);
lean_closure_set(v___f_3250_, 3, v___x_3247_);
lean_closure_set(v___f_3250_, 4, v___x_3227_);
lean_closure_set(v___f_3250_, 5, v___x_3228_);
lean_closure_set(v___f_3250_, 6, v___x_3248_);
lean_closure_set(v___f_3250_, 7, v_params_3230_);
lean_closure_set(v___f_3250_, 8, v_args_3231_);
lean_closure_set(v___f_3250_, 9, v_indices_3239_);
lean_closure_set(v___f_3250_, 10, v___x_3249_);
lean_closure_set(v___f_3250_, 11, v_a_3233_);
lean_closure_set(v___f_3250_, 12, v___x_3234_);
lean_closure_set(v___f_3250_, 13, v___x_3235_);
lean_closure_set(v___f_3250_, 14, v___f_3236_);
lean_closure_set(v___f_3250_, 15, v___x_3237_);
v___x_3251_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3240_, v___x_3238_, v___f_3250_, v___x_3232_, v___x_3232_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
return v___x_3251_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3223_ = stack[0].m_obj;
lean_object* v___x_3224_ = stack[1].m_obj;
lean_object* v___x_3225_ = stack[2].m_obj;
uint8_t v___x_3226_ = stack[3].m_num;
lean_object* v___x_3227_ = stack[4].m_obj;
lean_object* v___x_3228_ = stack[5].m_obj;
uint8_t v___x_3229_ = stack[6].m_num;
lean_object* v_params_3230_ = stack[7].m_obj;
lean_object* v_args_3231_ = stack[8].m_obj;
uint8_t v___x_3232_ = stack[9].m_num;
lean_object* v_a_3233_ = stack[10].m_obj;
lean_object* v___x_3234_ = stack[11].m_obj;
lean_object* v___x_3235_ = stack[12].m_obj;
lean_object* v___f_3236_ = stack[13].m_obj;
lean_object* v___x_3237_ = stack[14].m_obj;
lean_object* v___x_3238_ = stack[15].m_obj;
lean_object* v_indices_3239_ = stack[16].m_obj;
lean_object* v_goalType_3240_ = stack[17].m_obj;
lean_object* v___y_3241_ = stack[18].m_obj;
lean_object* v___y_3242_ = stack[19].m_obj;
lean_object* v___y_3243_ = stack[20].m_obj;
lean_object* v___y_3244_ = stack[21].m_obj;
lean_object* v_res_3252_;
v_res_3252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3223_, v___x_3224_, v___x_3225_, v___x_3226_, v___x_3227_, v___x_3228_, v___x_3229_, v_params_3230_, v_args_3231_, v___x_3232_, v_a_3233_, v___x_3234_, v___x_3235_, v___f_3236_, v___x_3237_, v___x_3238_, v_indices_3239_, v_goalType_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
stack->m_obj
 = v_res_3252_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3253_ = _args[0];
lean_object* v___x_3254_ = _args[1];
lean_object* v___x_3255_ = _args[2];
lean_object* v___x_3256_ = _args[3];
lean_object* v___x_3257_ = _args[4];
lean_object* v___x_3258_ = _args[5];
lean_object* v___x_3259_ = _args[6];
lean_object* v_params_3260_ = _args[7];
lean_object* v_args_3261_ = _args[8];
lean_object* v___x_3262_ = _args[9];
lean_object* v_a_3263_ = _args[10];
lean_object* v___x_3264_ = _args[11];
lean_object* v___x_3265_ = _args[12];
lean_object* v___f_3266_ = _args[13];
lean_object* v___x_3267_ = _args[14];
lean_object* v___x_3268_ = _args[15];
lean_object* v_indices_3269_ = _args[16];
lean_object* v_goalType_3270_ = _args[17];
lean_object* v___y_3271_ = _args[18];
lean_object* v___y_3272_ = _args[19];
lean_object* v___y_3273_ = _args[20];
lean_object* v___y_3274_ = _args[21];
lean_object* v___y_3275_ = _args[22];
_start:
{
uint8_t v___x_17395__boxed_3276_; uint8_t v___x_17398__boxed_3277_; uint8_t v___x_17399__boxed_3278_; lean_object* v_res_3279_; 
v___x_17395__boxed_3276_ = lean_unbox(v___x_3256_);
v___x_17398__boxed_3277_ = lean_unbox(v___x_3259_);
v___x_17399__boxed_3278_ = lean_unbox(v___x_3262_);
v_res_3279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3253_, v___x_3254_, v___x_3255_, v___x_17395__boxed_3276_, v___x_3257_, v___x_3258_, v___x_17398__boxed_3277_, v_params_3260_, v_args_3261_, v___x_17399__boxed_3278_, v_a_3263_, v___x_3264_, v___x_3265_, v___f_3266_, v___x_3267_, v___x_3268_, v_indices_3269_, v_goalType_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v_res_3279_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object* v___x_3280_, uint8_t v___x_3281_, lean_object* v_snd_3282_, lean_object* v___x_3283_, uint8_t v___x_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v_a_3287_, lean_object* v___x_3288_, lean_object* v___x_3289_, uint8_t v___x_3290_, lean_object* v___x_3291_, lean_object* v_params_3292_, lean_object* v_args_3293_, lean_object* v_a_3294_, lean_object* v___x_3295_, lean_object* v___x_3296_, lean_object* v___f_3297_, lean_object* v___x_3298_, lean_object* v___x_3299_, lean_object* v_numIndices_3300_, lean_object* v_goalType_3301_, lean_object* v___x_3302_, lean_object* v___x_3303_, lean_object* v_fst_3304_, lean_object* v___x_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_lctx_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; lean_object* v___x_3315_; uint8_t v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v_lctx_3311_ = lean_ctor_get(v___y_3306_, 2);
lean_inc(v___x_3280_);
lean_inc_ref(v_lctx_3311_);
v___x_3312_ = l_Lean_LocalContext_get_x21(v_lctx_3311_, v___x_3280_);
v___x_3313_ = l_Lean_LocalDecl_type(v___x_3312_);
lean_dec_ref(v___x_3312_);
v___x_3314_ = 2;
v___x_3315_ = lean_box(0);
v___x_3316_ = 0;
v___x_3317_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*1, v___x_3314_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*1 + 1, v___x_3281_);
lean_ctor_set_uint8(v___x_3317_, sizeof(void*)*1 + 2, v___x_3316_);
lean_inc_ref(v___x_3283_);
lean_inc(v_snd_3282_);
v___x_3318_ = l_Lean_MVarId_rewrite(v_snd_3282_, v___x_3313_, v___x_3283_, v___x_3281_, v___x_3317_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v_eNew_3320_; lean_object* v_eqProof_3321_; lean_object* v___x_3322_; lean_object* v___f_3323_; lean_object* v___x_3324_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v_eNew_3320_ = lean_ctor_get(v_a_3319_, 0);
lean_inc_ref(v_eNew_3320_);
v_eqProof_3321_ = lean_ctor_get(v_a_3319_, 1);
lean_inc_ref(v_eqProof_3321_);
lean_dec(v_a_3319_);
lean_inc(v___x_3280_);
v___x_3322_ = l_Lean_mkFVar(v___x_3280_);
lean_inc(v_snd_3282_);
v___f_3323_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3323_, 0, v_eqProof_3321_);
lean_closure_set(v___f_3323_, 1, v___x_3322_);
lean_closure_set(v___f_3323_, 2, v_eNew_3320_);
lean_closure_set(v___f_3323_, 3, v_snd_3282_);
lean_closure_set(v___f_3323_, 4, v___x_3280_);
v___x_3324_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3282_, v___f_3323_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___y_3327_; uint8_t v___x_3355_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v___x_3355_ = lean_nat_dec_lt(v___x_3302_, v___x_3303_);
if (v___x_3355_ == 0)
{
v___y_3327_ = v_fst_3304_;
goto v___jp_3326_;
}
else
{
lean_object* v_fvarId_3356_; lean_object* v_xs_x27_3357_; lean_object* v___x_3358_; 
v_fvarId_3356_ = lean_ctor_get(v_a_3325_, 0);
v_xs_x27_3357_ = lean_array_fset(v_fst_3304_, v___x_3302_, v___x_3305_);
lean_inc(v_fvarId_3356_);
v___x_3358_ = lean_array_fset(v_xs_x27_3357_, v___x_3302_, v_fvarId_3356_);
v___y_3327_ = v___x_3358_;
goto v___jp_3326_;
}
v___jp_3326_:
{
lean_object* v_mvarId_3328_; lean_object* v___x_3329_; 
v_mvarId_3328_ = lean_ctor_get(v_a_3325_, 1);
lean_inc(v_mvarId_3328_);
lean_dec(v_a_3325_);
v___x_3329_ = l_Lean_MVarId_revert(v_mvarId_3328_, v___y_3327_, v___x_3284_, v___x_3284_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v_snd_3331_; lean_object* v___x_3332_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3330_);
lean_dec_ref_known(v___x_3329_, 1);
v_snd_3331_ = lean_ctor_get(v_a_3330_, 1);
lean_inc(v_snd_3331_);
lean_dec(v_a_3330_);
v___x_3332_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3331_, v___x_3285_, v___y_3307_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3345_; 
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3345_ == 0)
{
lean_object* v_unused_3346_; 
v_unused_3346_ = lean_ctor_get(v___x_3332_, 0);
lean_dec(v_unused_3346_);
v___x_3334_ = v___x_3332_;
v_isShared_3335_ = v_isSharedCheck_3345_;
goto v_resetjp_3333_;
}
else
{
lean_dec(v___x_3332_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3345_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___f_3340_; lean_object* v___x_3342_; 
v___x_3336_ = l_Lean_Expr_app___override(v___x_3286_, v_a_3287_);
v___x_3337_ = lean_box(v___x_3290_);
v___x_3338_ = lean_box(v___x_3281_);
v___x_3339_ = lean_box(v___x_3284_);
v___f_3340_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 23, 16);
lean_closure_set(v___f_3340_, 0, v___x_3336_);
lean_closure_set(v___f_3340_, 1, v___x_3288_);
lean_closure_set(v___f_3340_, 2, v___x_3289_);
lean_closure_set(v___f_3340_, 3, v___x_3337_);
lean_closure_set(v___f_3340_, 4, v___x_3291_);
lean_closure_set(v___f_3340_, 5, v___x_3283_);
lean_closure_set(v___f_3340_, 6, v___x_3338_);
lean_closure_set(v___f_3340_, 7, v_params_3292_);
lean_closure_set(v___f_3340_, 8, v_args_3293_);
lean_closure_set(v___f_3340_, 9, v___x_3339_);
lean_closure_set(v___f_3340_, 10, v_a_3294_);
lean_closure_set(v___f_3340_, 11, v___x_3295_);
lean_closure_set(v___f_3340_, 12, v___x_3296_);
lean_closure_set(v___f_3340_, 13, v___f_3297_);
lean_closure_set(v___f_3340_, 14, v___x_3298_);
lean_closure_set(v___f_3340_, 15, v___x_3299_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set_tag(v___x_3334_, 1);
lean_ctor_set(v___x_3334_, 0, v_numIndices_3300_);
v___x_3342_ = v___x_3334_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_numIndices_3300_);
v___x_3342_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3343_; 
v___x_3343_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3301_, v___x_3342_, v___f_3340_, v___x_3284_, v___x_3284_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec_ref(v___y_3306_);
return v___x_3343_;
}
}
}
else
{
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_goalType_3301_);
lean_dec(v_numIndices_3300_);
lean_dec(v___x_3299_);
lean_dec(v___x_3298_);
lean_dec_ref(v___f_3297_);
lean_dec_ref(v___x_3296_);
lean_dec(v___x_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_args_3293_);
lean_dec_ref(v_params_3292_);
lean_dec(v___x_3291_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
lean_dec_ref(v_a_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3283_);
return v___x_3332_;
}
}
else
{
lean_object* v_a_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3354_; 
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_goalType_3301_);
lean_dec(v_numIndices_3300_);
lean_dec(v___x_3299_);
lean_dec(v___x_3298_);
lean_dec_ref(v___f_3297_);
lean_dec_ref(v___x_3296_);
lean_dec(v___x_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_args_3293_);
lean_dec_ref(v_params_3292_);
lean_dec(v___x_3291_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
lean_dec_ref(v_a_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3283_);
v_a_3347_ = lean_ctor_get(v___x_3329_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3329_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3329_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3329_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3352_; 
if (v_isShared_3350_ == 0)
{
v___x_3352_ = v___x_3349_;
goto v_reusejp_3351_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v_a_3347_);
v___x_3352_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3351_;
}
v_reusejp_3351_:
{
return v___x_3352_;
}
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_fst_3304_);
lean_dec_ref(v_goalType_3301_);
lean_dec(v_numIndices_3300_);
lean_dec(v___x_3299_);
lean_dec(v___x_3298_);
lean_dec_ref(v___f_3297_);
lean_dec_ref(v___x_3296_);
lean_dec(v___x_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_args_3293_);
lean_dec_ref(v_params_3292_);
lean_dec(v___x_3291_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
lean_dec_ref(v_a_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3283_);
v_a_3359_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3324_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3324_);
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
lean_dec_ref(v___y_3306_);
lean_dec_ref(v_fst_3304_);
lean_dec_ref(v_goalType_3301_);
lean_dec(v_numIndices_3300_);
lean_dec(v___x_3299_);
lean_dec(v___x_3298_);
lean_dec_ref(v___f_3297_);
lean_dec_ref(v___x_3296_);
lean_dec(v___x_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_args_3293_);
lean_dec_ref(v_params_3292_);
lean_dec(v___x_3291_);
lean_dec(v___x_3289_);
lean_dec(v___x_3288_);
lean_dec_ref(v_a_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3283_);
lean_dec(v_snd_3282_);
lean_dec(v___x_3280_);
v_a_3367_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3318_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3318_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3280_ = stack[0].m_obj;
uint8_t v___x_3281_ = stack[1].m_num;
lean_object* v_snd_3282_ = stack[2].m_obj;
lean_object* v___x_3283_ = stack[3].m_obj;
uint8_t v___x_3284_ = stack[4].m_num;
lean_object* v___x_3285_ = stack[5].m_obj;
lean_object* v___x_3286_ = stack[6].m_obj;
lean_object* v_a_3287_ = stack[7].m_obj;
lean_object* v___x_3288_ = stack[8].m_obj;
lean_object* v___x_3289_ = stack[9].m_obj;
uint8_t v___x_3290_ = stack[10].m_num;
lean_object* v___x_3291_ = stack[11].m_obj;
lean_object* v_params_3292_ = stack[12].m_obj;
lean_object* v_args_3293_ = stack[13].m_obj;
lean_object* v_a_3294_ = stack[14].m_obj;
lean_object* v___x_3295_ = stack[15].m_obj;
lean_object* v___x_3296_ = stack[16].m_obj;
lean_object* v___f_3297_ = stack[17].m_obj;
lean_object* v___x_3298_ = stack[18].m_obj;
lean_object* v___x_3299_ = stack[19].m_obj;
lean_object* v_numIndices_3300_ = stack[20].m_obj;
lean_object* v_goalType_3301_ = stack[21].m_obj;
lean_object* v___x_3302_ = stack[22].m_obj;
lean_object* v___x_3303_ = stack[23].m_obj;
lean_object* v_fst_3304_ = stack[24].m_obj;
lean_object* v___x_3305_ = stack[25].m_obj;
lean_object* v___y_3306_ = stack[26].m_obj;
lean_object* v___y_3307_ = stack[27].m_obj;
lean_object* v___y_3308_ = stack[28].m_obj;
lean_object* v___y_3309_ = stack[29].m_obj;
lean_object* v_res_3375_;
v_res_3375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3280_, v___x_3281_, v_snd_3282_, v___x_3283_, v___x_3284_, v___x_3285_, v___x_3286_, v_a_3287_, v___x_3288_, v___x_3289_, v___x_3290_, v___x_3291_, v_params_3292_, v_args_3293_, v_a_3294_, v___x_3295_, v___x_3296_, v___f_3297_, v___x_3298_, v___x_3299_, v_numIndices_3300_, v_goalType_3301_, v___x_3302_, v___x_3303_, v_fst_3304_, v___x_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
stack->m_obj
 = v_res_3375_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object** _args){
lean_object* v___x_3376_ = _args[0];
lean_object* v___x_3377_ = _args[1];
lean_object* v_snd_3378_ = _args[2];
lean_object* v___x_3379_ = _args[3];
lean_object* v___x_3380_ = _args[4];
lean_object* v___x_3381_ = _args[5];
lean_object* v___x_3382_ = _args[6];
lean_object* v_a_3383_ = _args[7];
lean_object* v___x_3384_ = _args[8];
lean_object* v___x_3385_ = _args[9];
lean_object* v___x_3386_ = _args[10];
lean_object* v___x_3387_ = _args[11];
lean_object* v_params_3388_ = _args[12];
lean_object* v_args_3389_ = _args[13];
lean_object* v_a_3390_ = _args[14];
lean_object* v___x_3391_ = _args[15];
lean_object* v___x_3392_ = _args[16];
lean_object* v___f_3393_ = _args[17];
lean_object* v___x_3394_ = _args[18];
lean_object* v___x_3395_ = _args[19];
lean_object* v_numIndices_3396_ = _args[20];
lean_object* v_goalType_3397_ = _args[21];
lean_object* v___x_3398_ = _args[22];
lean_object* v___x_3399_ = _args[23];
lean_object* v_fst_3400_ = _args[24];
lean_object* v___x_3401_ = _args[25];
lean_object* v___y_3402_ = _args[26];
lean_object* v___y_3403_ = _args[27];
lean_object* v___y_3404_ = _args[28];
lean_object* v___y_3405_ = _args[29];
lean_object* v___y_3406_ = _args[30];
_start:
{
uint8_t v___x_17506__boxed_3407_; uint8_t v___x_17509__boxed_3408_; uint8_t v___x_17515__boxed_3409_; lean_object* v_res_3410_; 
v___x_17506__boxed_3407_ = lean_unbox(v___x_3377_);
v___x_17509__boxed_3408_ = lean_unbox(v___x_3380_);
v___x_17515__boxed_3409_ = lean_unbox(v___x_3386_);
v_res_3410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3376_, v___x_17506__boxed_3407_, v_snd_3378_, v___x_3379_, v___x_17509__boxed_3408_, v___x_3381_, v___x_3382_, v_a_3383_, v___x_3384_, v___x_3385_, v___x_17515__boxed_3409_, v___x_3387_, v_params_3388_, v_args_3389_, v_a_3390_, v___x_3391_, v___x_3392_, v___f_3393_, v___x_3394_, v___x_3395_, v_numIndices_3396_, v_goalType_3397_, v___x_3398_, v___x_3399_, v_fst_3400_, v___x_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec(v___x_3399_);
lean_dec(v___x_3398_);
return v_res_3410_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t v___x_3411_, lean_object* v_x_3412_){
_start:
{
return v___x_3411_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_3411_ = stack[0].m_num;
lean_object* v_x_3412_ = stack[1].m_obj;
uint8_t v_res_3413_;
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_3411_, v_x_3412_);
stack->m_num = v_res_3413_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object* v___x_3414_, lean_object* v_x_3415_){
_start:
{
uint8_t v___x_17817__boxed_3416_; uint8_t v_res_3417_; lean_object* v_r_3418_; 
v___x_17817__boxed_3416_ = lean_unbox(v___x_3414_);
v_res_3417_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_17817__boxed_3416_, v_x_3415_);
lean_dec(v_x_3415_);
v_r_3418_ = lean_box(v_res_3417_);
return v_r_3418_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object* v___x_3422_, lean_object* v_a_3423_, lean_object* v___x_3424_, lean_object* v_numIndices_3425_, lean_object* v___x_3426_, lean_object* v___x_3427_, lean_object* v___x_3428_, lean_object* v_params_3429_, lean_object* v_a_3430_, lean_object* v___x_3431_, lean_object* v___x_3432_, lean_object* v___x_3433_, lean_object* v___x_3434_, lean_object* v_args_3435_, lean_object* v_goalType_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = lean_array_get_size(v_args_3435_);
v___x_3443_ = lean_nat_dec_eq(v___x_3442_, v___x_3422_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
lean_dec_ref(v_goalType_3436_);
lean_dec_ref(v_args_3435_);
lean_dec(v___x_3433_);
lean_dec_ref(v___x_3432_);
lean_dec(v___x_3431_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_params_3429_);
lean_dec_ref(v___x_3428_);
lean_dec_ref(v___x_3427_);
lean_dec(v_numIndices_3425_);
lean_dec(v___x_3424_);
lean_dec(v___x_3422_);
v___x_3444_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3445_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3444_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3445_;
}
else
{
if (lean_obj_tag(v_a_3423_) == 7)
{
lean_object* v_binderType_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; uint8_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v_binderType_3446_ = lean_ctor_get(v_a_3423_, 1);
v___x_3447_ = lean_array_fget(v_args_3435_, v___x_3424_);
lean_inc_ref(v_binderType_3446_);
v___x_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_binderType_3446_);
v___x_3449_ = 0;
v___x_3450_ = lean_box(0);
v___x_3451_ = l_Lean_Meta_mkFreshExprMVar(v___x_3448_, v___x_3449_, v___x_3450_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; lean_object* v___f_3457_; lean_object* v___x_3458_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = l_Lean_Expr_mvarId_x21(v_a_3452_);
v___x_3454_ = lean_nat_add(v_numIndices_3425_, v___x_3422_);
v___x_3455_ = lean_box(0);
v___x_3456_ = 0;
v___f_3457_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0));
v___x_3458_ = l_Lean_Meta_introNCore(v___x_3453_, v___x_3454_, v___x_3455_, v___x_3456_, v___x_3456_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v_fst_3460_; lean_object* v_snd_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___f_3468_; lean_object* v___x_3469_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v_fst_3460_ = lean_ctor_get(v_a_3459_, 0);
lean_inc(v_fst_3460_);
v_snd_3461_ = lean_ctor_get(v_a_3459_, 1);
lean_inc_n(v_snd_3461_, 2);
lean_dec(v_a_3459_);
v___x_3462_ = lean_array_get_size(v_fst_3460_);
v___x_3463_ = lean_nat_sub(v___x_3462_, v___x_3422_);
v___x_3464_ = lean_array_get(v___x_3426_, v_fst_3460_, v___x_3463_);
v___x_3465_ = lean_box(v___x_3443_);
v___x_3466_ = lean_box(v___x_3456_);
v___x_3467_ = lean_box(v___x_3449_);
v___f_3468_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed), 31, 26);
lean_closure_set(v___f_3468_, 0, v___x_3464_);
lean_closure_set(v___f_3468_, 1, v___x_3465_);
lean_closure_set(v___f_3468_, 2, v_snd_3461_);
lean_closure_set(v___f_3468_, 3, v___x_3427_);
lean_closure_set(v___f_3468_, 4, v___x_3466_);
lean_closure_set(v___f_3468_, 5, v___x_3447_);
lean_closure_set(v___f_3468_, 6, v___x_3428_);
lean_closure_set(v___f_3468_, 7, v_a_3452_);
lean_closure_set(v___f_3468_, 8, v___x_3422_);
lean_closure_set(v___f_3468_, 9, v___x_3424_);
lean_closure_set(v___f_3468_, 10, v___x_3467_);
lean_closure_set(v___f_3468_, 11, v___x_3450_);
lean_closure_set(v___f_3468_, 12, v_params_3429_);
lean_closure_set(v___f_3468_, 13, v_args_3435_);
lean_closure_set(v___f_3468_, 14, v_a_3430_);
lean_closure_set(v___f_3468_, 15, v___x_3431_);
lean_closure_set(v___f_3468_, 16, v___x_3432_);
lean_closure_set(v___f_3468_, 17, v___f_3457_);
lean_closure_set(v___f_3468_, 18, v___x_3455_);
lean_closure_set(v___f_3468_, 19, v___x_3433_);
lean_closure_set(v___f_3468_, 20, v_numIndices_3425_);
lean_closure_set(v___f_3468_, 21, v_goalType_3436_);
lean_closure_set(v___f_3468_, 22, v___x_3463_);
lean_closure_set(v___f_3468_, 23, v___x_3462_);
lean_closure_set(v___f_3468_, 24, v_fst_3460_);
lean_closure_set(v___f_3468_, 25, v___x_3434_);
v___x_3469_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3461_, v___f_3468_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3469_;
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec(v_a_3452_);
lean_dec(v___x_3447_);
lean_dec_ref(v_goalType_3436_);
lean_dec_ref(v_args_3435_);
lean_dec(v___x_3433_);
lean_dec_ref(v___x_3432_);
lean_dec(v___x_3431_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_params_3429_);
lean_dec_ref(v___x_3428_);
lean_dec_ref(v___x_3427_);
lean_dec(v_numIndices_3425_);
lean_dec(v___x_3424_);
lean_dec(v___x_3422_);
v_a_3470_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3458_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3458_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3485_; 
lean_dec(v___x_3447_);
lean_dec_ref(v_goalType_3436_);
lean_dec_ref(v_args_3435_);
lean_dec(v___x_3433_);
lean_dec_ref(v___x_3432_);
lean_dec(v___x_3431_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_params_3429_);
lean_dec_ref(v___x_3428_);
lean_dec_ref(v___x_3427_);
lean_dec(v_numIndices_3425_);
lean_dec(v___x_3424_);
lean_dec(v___x_3422_);
v_a_3478_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3480_ = v___x_3451_;
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3451_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3485_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
if (v_isShared_3481_ == 0)
{
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
else
{
lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_dec_ref(v_goalType_3436_);
lean_dec_ref(v_args_3435_);
lean_dec(v___x_3433_);
lean_dec_ref(v___x_3432_);
lean_dec(v___x_3431_);
lean_dec_ref(v_a_3430_);
lean_dec_ref(v_params_3429_);
lean_dec_ref(v___x_3428_);
lean_dec_ref(v___x_3427_);
lean_dec(v_numIndices_3425_);
lean_dec(v___x_3424_);
lean_dec(v___x_3422_);
v___x_3486_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3487_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3486_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
return v___x_3487_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3422_ = stack[0].m_obj;
lean_object* v_a_3423_ = stack[1].m_obj;
lean_object* v___x_3424_ = stack[2].m_obj;
lean_object* v_numIndices_3425_ = stack[3].m_obj;
lean_object* v___x_3426_ = stack[4].m_obj;
lean_object* v___x_3427_ = stack[5].m_obj;
lean_object* v___x_3428_ = stack[6].m_obj;
lean_object* v_params_3429_ = stack[7].m_obj;
lean_object* v_a_3430_ = stack[8].m_obj;
lean_object* v___x_3431_ = stack[9].m_obj;
lean_object* v___x_3432_ = stack[10].m_obj;
lean_object* v___x_3433_ = stack[11].m_obj;
lean_object* v___x_3434_ = stack[12].m_obj;
lean_object* v_args_3435_ = stack[13].m_obj;
lean_object* v_goalType_3436_ = stack[14].m_obj;
lean_object* v___y_3437_ = stack[15].m_obj;
lean_object* v___y_3438_ = stack[16].m_obj;
lean_object* v___y_3439_ = stack[17].m_obj;
lean_object* v___y_3440_ = stack[18].m_obj;
lean_object* v_res_3488_;
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3422_, v_a_3423_, v___x_3424_, v_numIndices_3425_, v___x_3426_, v___x_3427_, v___x_3428_, v_params_3429_, v_a_3430_, v___x_3431_, v___x_3432_, v___x_3433_, v___x_3434_, v_args_3435_, v_goalType_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
stack->m_obj
 = v_res_3488_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object** _args){
lean_object* v___x_3489_ = _args[0];
lean_object* v_a_3490_ = _args[1];
lean_object* v___x_3491_ = _args[2];
lean_object* v_numIndices_3492_ = _args[3];
lean_object* v___x_3493_ = _args[4];
lean_object* v___x_3494_ = _args[5];
lean_object* v___x_3495_ = _args[6];
lean_object* v_params_3496_ = _args[7];
lean_object* v_a_3497_ = _args[8];
lean_object* v___x_3498_ = _args[9];
lean_object* v___x_3499_ = _args[10];
lean_object* v___x_3500_ = _args[11];
lean_object* v___x_3501_ = _args[12];
lean_object* v_args_3502_ = _args[13];
lean_object* v_goalType_3503_ = _args[14];
lean_object* v___y_3504_ = _args[15];
lean_object* v___y_3505_ = _args[16];
lean_object* v___y_3506_ = _args[17];
lean_object* v___y_3507_ = _args[18];
lean_object* v___y_3508_ = _args[19];
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3489_, v_a_3490_, v___x_3491_, v_numIndices_3492_, v___x_3493_, v___x_3494_, v___x_3495_, v_params_3496_, v_a_3497_, v___x_3498_, v___x_3499_, v___x_3500_, v___x_3501_, v_args_3502_, v_goalType_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___x_3493_);
lean_dec_ref(v_a_3490_);
return v_res_3509_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v___x_3516_; lean_object* v_env_3517_; uint8_t v___x_3518_; lean_object* v___x_3519_; 
v___x_3516_ = lean_st_ref_get(v___y_3514_);
v_env_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc_ref(v_env_3517_);
lean_dec(v___x_3516_);
v___x_3518_ = 0;
lean_inc(v_constName_3510_);
v___x_3519_ = l_Lean_Environment_findConstVal_x3f(v_env_3517_, v_constName_3510_, v___x_3518_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
return v___x_3520_;
}
else
{
lean_object* v_val_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec(v_constName_3510_);
v_val_3521_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3519_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_val_3521_);
lean_dec(v___x_3519_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
lean_ctor_set_tag(v___x_3523_, 0);
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_val_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3510_ = stack[0].m_obj;
lean_object* v___y_3511_ = stack[1].m_obj;
lean_object* v___y_3512_ = stack[2].m_obj;
lean_object* v___y_3513_ = stack[3].m_obj;
lean_object* v___y_3514_ = stack[4].m_obj;
lean_object* v_res_3529_;
v_res_3529_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
stack->m_obj
 = v_res_3529_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3536_;
}
}
lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___x_3543_; 
lean_inc(v_constName_3537_);
v___x_3543_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3555_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3555_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3555_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v_levelParams_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3553_; 
v_levelParams_3548_ = lean_ctor_get(v_a_3544_, 1);
lean_inc(v_levelParams_3548_);
lean_dec(v_a_3544_);
v___x_3549_ = lean_box(0);
v___x_3550_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3548_, v___x_3549_);
v___x_3551_ = l_Lean_mkConst(v_constName_3537_, v___x_3550_);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3551_);
v___x_3553_ = v___x_3546_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3551_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_constName_3537_);
v_a_3556_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3543_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3543_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3537_ = stack[0].m_obj;
lean_object* v___y_3538_ = stack[1].m_obj;
lean_object* v___y_3539_ = stack[2].m_obj;
lean_object* v___y_3540_ = stack[3].m_obj;
lean_object* v___y_3541_ = stack[4].m_obj;
lean_object* v_res_3564_;
v_res_3564_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_);
stack->m_obj
 = v_res_3564_;
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3565_, v___y_3566_, v___y_3567_, v___y_3568_, v___y_3569_);
lean_dec(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec(v___y_3567_);
lean_dec_ref(v___y_3566_);
return v_res_3571_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v___y_3574_, lean_object* v_levels_3575_, lean_object* v_params_3576_, lean_object* v_predicates_3577_, lean_object* v_as_3578_, size_t v_sz_3579_, size_t v_i_3580_, lean_object* v_b_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
uint8_t v___x_3587_; 
v___x_3587_ = lean_usize_dec_lt(v_i_3580_, v_sz_3579_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; 
lean_dec_ref(v_params_3576_);
lean_dec(v_levels_3575_);
lean_dec_ref(v___y_3574_);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v_b_3581_);
return v___x_3588_;
}
else
{
lean_object* v_a_3589_; lean_object* v_toConstantVal_3590_; lean_object* v_numParams_3591_; lean_object* v_numIndices_3592_; lean_object* v_name_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___f_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_a_3589_ = lean_array_uget_borrowed(v_as_3578_, v_i_3580_);
v_toConstantVal_3590_ = lean_ctor_get(v_a_3589_, 0);
v_numParams_3591_ = lean_ctor_get(v_a_3589_, 1);
v_numIndices_3592_ = lean_ctor_get(v_a_3589_, 2);
v_name_3593_ = lean_ctor_get(v_toConstantVal_3590_, 0);
v___x_3594_ = lean_unsigned_to_nat(0u);
v___x_3595_ = lean_box(0);
v___x_3596_ = lean_box(0);
lean_inc_ref(v_params_3576_);
lean_inc(v_levels_3575_);
lean_inc_ref(v___y_3574_);
lean_inc_n(v_name_3593_, 2);
lean_inc(v_numParams_3591_);
v___f_3597_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3597_, 0, v_numParams_3591_);
lean_closure_set(v___f_3597_, 1, v_name_3593_);
lean_closure_set(v___f_3597_, 2, v___y_3574_);
lean_closure_set(v___f_3597_, 3, v___x_3594_);
lean_closure_set(v___f_3597_, 4, v_levels_3575_);
lean_closure_set(v___f_3597_, 5, v_params_3576_);
v___x_3598_ = l_Lean_mkCasesOnName(v_name_3593_);
lean_inc(v___x_3598_);
v___x_3599_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3598_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3598_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc(v_a_3602_);
lean_dec_ref_known(v___x_3601_, 1);
lean_inc_ref(v_params_3576_);
v___x_3603_ = l_Array_append___redArg(v_params_3576_, v_predicates_3577_);
v___x_3604_ = l_Lean_mkAppN(v_a_3602_, v___x_3603_);
lean_dec_ref(v___x_3603_);
lean_inc(v___y_3585_);
lean_inc_ref(v___y_3584_);
lean_inc(v___y_3583_);
lean_inc_ref(v___y_3582_);
lean_inc_ref(v___x_3604_);
v___x_3605_ = lean_infer_type(v___x_3604_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v___x_3607_ = lean_replace_expr(v___f_3597_, v_a_3606_);
lean_dec(v_a_3606_);
lean_dec_ref(v___f_3597_);
lean_inc(v___y_3585_);
lean_inc_ref(v___y_3584_);
lean_inc(v___y_3583_);
lean_inc_ref(v___y_3582_);
lean_inc_ref(v___x_3604_);
v___x_3608_ = lean_infer_type(v___x_3604_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___f_3616_; uint8_t v___x_3617_; lean_object* v___x_3618_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
lean_inc(v_name_3593_);
v___x_3610_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3593_);
v___x_3611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3610_);
v___x_3612_ = l_Lean_Name_append(v___x_3610_, v___x_3611_);
lean_inc(v_levels_3575_);
v___x_3613_ = l_Lean_mkConst(v___x_3612_, v_levels_3575_);
v___x_3614_ = lean_unsigned_to_nat(1u);
v___x_3615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3607_);
lean_inc_ref(v_params_3576_);
lean_inc(v_numIndices_3592_);
v___f_3616_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed), 20, 13);
lean_closure_set(v___f_3616_, 0, v___x_3614_);
lean_closure_set(v___f_3616_, 1, v_a_3609_);
lean_closure_set(v___f_3616_, 2, v___x_3594_);
lean_closure_set(v___f_3616_, 3, v_numIndices_3592_);
lean_closure_set(v___f_3616_, 4, v___x_3595_);
lean_closure_set(v___f_3616_, 5, v___x_3613_);
lean_closure_set(v___f_3616_, 6, v___x_3604_);
lean_closure_set(v___f_3616_, 7, v_params_3576_);
lean_closure_set(v___f_3616_, 8, v_a_3600_);
lean_closure_set(v___f_3616_, 9, v___x_3610_);
lean_closure_set(v___f_3616_, 10, v___x_3607_);
lean_closure_set(v___f_3616_, 11, v___x_3615_);
lean_closure_set(v___f_3616_, 12, v___x_3596_);
v___x_3617_ = 0;
v___x_3618_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_3607_, v___x_3615_, v___f_3616_, v___x_3617_, v___x_3617_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
if (lean_obj_tag(v___x_3618_) == 0)
{
size_t v___x_3619_; size_t v___x_3620_; 
lean_dec_ref_known(v___x_3618_, 1);
v___x_3619_ = ((size_t)1ULL);
v___x_3620_ = lean_usize_add(v_i_3580_, v___x_3619_);
v_i_3580_ = v___x_3620_;
v_b_3581_ = v___x_3596_;
goto _start;
}
else
{
lean_dec_ref(v_params_3576_);
lean_dec(v_levels_3575_);
lean_dec_ref(v___y_3574_);
return v___x_3618_;
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_dec_ref(v___x_3607_);
lean_dec_ref(v___x_3604_);
lean_dec(v_a_3600_);
lean_dec_ref(v_params_3576_);
lean_dec(v_levels_3575_);
lean_dec_ref(v___y_3574_);
v_a_3622_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3608_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3608_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref(v___x_3604_);
lean_dec(v_a_3600_);
lean_dec_ref(v___f_3597_);
lean_dec_ref(v_params_3576_);
lean_dec(v_levels_3575_);
lean_dec_ref(v___y_3574_);
v_a_3630_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3605_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3605_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v_a_3600_);
lean_dec_ref(v___f_3597_);
lean_dec_ref(v_params_3576_);
lean_dec(v_levels_3575_);
lean_dec_ref(v___y_3574_);
v_a_3638_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3601_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3601_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec(v___x_3598_);
lean_dec_ref(v___f_3597_);
lean_dec_ref(v_params_3576_);
lean_dec(v_levels_3575_);
lean_dec_ref(v___y_3574_);
v_a_3646_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3599_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3599_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_3574_ = stack[0].m_obj;
lean_object* v_levels_3575_ = stack[1].m_obj;
lean_object* v_params_3576_ = stack[2].m_obj;
lean_object* v_predicates_3577_ = stack[3].m_obj;
lean_object* v_as_3578_ = stack[4].m_obj;
size_t v_sz_3579_ = stack[5].m_num;
size_t v_i_3580_ = stack[6].m_num;
lean_object* v_b_3581_ = stack[7].m_obj;
lean_object* v___y_3582_ = stack[8].m_obj;
lean_object* v___y_3583_ = stack[9].m_obj;
lean_object* v___y_3584_ = stack[10].m_obj;
lean_object* v___y_3585_ = stack[11].m_obj;
lean_object* v_res_3654_;
v_res_3654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3574_, v_levels_3575_, v_params_3576_, v_predicates_3577_, v_as_3578_, v_sz_3579_, v_i_3580_, v_b_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
stack->m_obj
 = v_res_3654_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v___y_3655_, lean_object* v_levels_3656_, lean_object* v_params_3657_, lean_object* v_predicates_3658_, lean_object* v_as_3659_, lean_object* v_sz_3660_, lean_object* v_i_3661_, lean_object* v_b_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
size_t v_sz_boxed_3668_; size_t v_i_boxed_3669_; lean_object* v_res_3670_; 
v_sz_boxed_3668_ = lean_unbox_usize(v_sz_3660_);
lean_dec(v_sz_3660_);
v_i_boxed_3669_ = lean_unbox_usize(v_i_3661_);
lean_dec(v_i_3661_);
v_res_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3655_, v_levels_3656_, v_params_3657_, v_predicates_3658_, v_as_3659_, v_sz_boxed_3668_, v_i_boxed_3669_, v_b_3662_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec_ref(v_as_3659_);
lean_dec_ref(v_predicates_3658_);
return v_res_3670_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3671_, size_t v_sz_3672_, size_t v_i_3673_, lean_object* v_bs_3674_){
_start:
{
uint8_t v___x_3675_; 
v___x_3675_ = lean_usize_dec_lt(v_i_3673_, v_sz_3672_);
if (v___x_3675_ == 0)
{
lean_dec(v_levels_3671_);
return v_bs_3674_;
}
else
{
lean_object* v_v_3676_; lean_object* v_toConstantVal_3677_; lean_object* v_name_3678_; lean_object* v___x_3679_; lean_object* v_bs_x27_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; size_t v___x_3683_; size_t v___x_3684_; lean_object* v___x_3685_; 
v_v_3676_ = lean_array_uget_borrowed(v_bs_3674_, v_i_3673_);
v_toConstantVal_3677_ = lean_ctor_get(v_v_3676_, 0);
v_name_3678_ = lean_ctor_get(v_toConstantVal_3677_, 0);
lean_inc(v_name_3678_);
v___x_3679_ = lean_unsigned_to_nat(0u);
v_bs_x27_3680_ = lean_array_uset(v_bs_3674_, v_i_3673_, v___x_3679_);
v___x_3681_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3678_);
lean_inc(v_levels_3671_);
v___x_3682_ = l_Lean_mkConst(v___x_3681_, v_levels_3671_);
v___x_3683_ = ((size_t)1ULL);
v___x_3684_ = lean_usize_add(v_i_3673_, v___x_3683_);
v___x_3685_ = lean_array_uset(v_bs_x27_3680_, v_i_3673_, v___x_3682_);
v_i_3673_ = v___x_3684_;
v_bs_3674_ = v___x_3685_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_levels_3671_ = stack[0].m_obj;
size_t v_sz_3672_ = stack[1].m_num;
size_t v_i_3673_ = stack[2].m_num;
lean_object* v_bs_3674_ = stack[3].m_obj;
lean_object* v_res_3687_;
v_res_3687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3671_, v_sz_3672_, v_i_3673_, v_bs_3674_);
stack->m_obj
 = v_res_3687_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3688_, lean_object* v_sz_3689_, lean_object* v_i_3690_, lean_object* v_bs_3691_){
_start:
{
size_t v_sz_boxed_3692_; size_t v_i_boxed_3693_; lean_object* v_res_3694_; 
v_sz_boxed_3692_ = lean_unbox_usize(v_sz_3689_);
lean_dec(v_sz_3689_);
v_i_boxed_3693_ = lean_unbox_usize(v_i_3690_);
lean_dec(v_i_3690_);
v_res_3694_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3688_, v_sz_boxed_3692_, v_i_boxed_3693_, v_bs_3691_);
return v_res_3694_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3695_, lean_object* v_levels_3696_, lean_object* v___y_3697_, lean_object* v_params_3698_, lean_object* v_x_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
size_t v_sz_3705_; size_t v___x_3706_; lean_object* v_predicates_3707_; size_t v_sz_3708_; lean_object* v_predicates_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_sz_3705_ = lean_array_size(v_infos_3695_);
v___x_3706_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3695_);
lean_inc(v_levels_3696_);
v_predicates_3707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3696_, v_sz_3705_, v___x_3706_, v_infos_3695_);
v_sz_3708_ = lean_array_size(v_predicates_3707_);
v_predicates_3709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3698_, v_sz_3708_, v___x_3706_, v_predicates_3707_);
v___x_3710_ = lean_box(0);
v___x_3711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v___y_3697_, v_levels_3696_, v_params_3698_, v_predicates_3709_, v_infos_3695_, v_sz_3705_, v___x_3706_, v___x_3710_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec_ref(v_infos_3695_);
lean_dec_ref(v_predicates_3709_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; 
v_unused_3719_ = lean_ctor_get(v___x_3711_, 0);
lean_dec(v_unused_3719_);
v___x_3713_ = v___x_3711_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_dec(v___x_3711_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 0, v___x_3710_);
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3710_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
else
{
return v___x_3711_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_3695_ = stack[0].m_obj;
lean_object* v_levels_3696_ = stack[1].m_obj;
lean_object* v___y_3697_ = stack[2].m_obj;
lean_object* v_params_3698_ = stack[3].m_obj;
lean_object* v_x_3699_ = stack[4].m_obj;
lean_object* v___y_3700_ = stack[5].m_obj;
lean_object* v___y_3701_ = stack[6].m_obj;
lean_object* v___y_3702_ = stack[7].m_obj;
lean_object* v___y_3703_ = stack[8].m_obj;
lean_object* v_res_3720_;
v_res_3720_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3695_, v_levels_3696_, v___y_3697_, v_params_3698_, v_x_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
stack->m_obj
 = v_res_3720_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3721_, lean_object* v_levels_3722_, lean_object* v___y_3723_, lean_object* v_params_3724_, lean_object* v_x_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3721_, v_levels_3722_, v___y_3723_, v_params_3724_, v_x_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
lean_dec(v___y_3727_);
lean_dec_ref(v___y_3726_);
lean_dec_ref(v_x_3725_);
return v_res_3731_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3732_, size_t v_i_3733_, size_t v_stop_3734_, lean_object* v_b_3735_){
_start:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_usize_dec_eq(v_i_3733_, v_stop_3734_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; lean_object* v_ctors_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; size_t v___x_3741_; size_t v___x_3742_; 
v___x_3737_ = lean_array_uget_borrowed(v_as_3732_, v_i_3733_);
v_ctors_3738_ = lean_ctor_get(v___x_3737_, 4);
lean_inc(v_ctors_3738_);
v___x_3739_ = lean_array_mk(v_ctors_3738_);
v___x_3740_ = l_Array_append___redArg(v_b_3735_, v___x_3739_);
lean_dec_ref(v___x_3739_);
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = lean_usize_add(v_i_3733_, v___x_3741_);
v_i_3733_ = v___x_3742_;
v_b_3735_ = v___x_3740_;
goto _start;
}
else
{
return v_b_3735_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3732_ = stack[0].m_obj;
size_t v_i_3733_ = stack[1].m_num;
size_t v_stop_3734_ = stack[2].m_num;
lean_object* v_b_3735_ = stack[3].m_obj;
lean_object* v_res_3744_;
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3732_, v_i_3733_, v_stop_3734_, v_b_3735_);
stack->m_obj
 = v_res_3744_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3745_, lean_object* v_i_3746_, lean_object* v_stop_3747_, lean_object* v_b_3748_){
_start:
{
size_t v_i_boxed_3749_; size_t v_stop_boxed_3750_; lean_object* v_res_3751_; 
v_i_boxed_3749_ = lean_unbox_usize(v_i_3746_);
lean_dec(v_i_3746_);
v_stop_boxed_3750_ = lean_unbox_usize(v_stop_3747_);
lean_dec(v_stop_3747_);
v_res_3751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3745_, v_i_boxed_3749_, v_stop_boxed_3750_, v_b_3748_);
lean_dec_ref(v_as_3745_);
return v_res_3751_;
}
}
lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v_toConstantVal_3763_; lean_object* v_numParams_3764_; lean_object* v_levelParams_3765_; lean_object* v_type_3766_; lean_object* v___x_3767_; lean_object* v_levels_3768_; lean_object* v___y_3770_; lean_object* v___x_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
v___x_3760_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3761_ = lean_unsigned_to_nat(0u);
v___x_3762_ = lean_array_get_borrowed(v___x_3760_, v_infos_3754_, v___x_3761_);
v_toConstantVal_3763_ = lean_ctor_get(v___x_3762_, 0);
v_numParams_3764_ = lean_ctor_get(v___x_3762_, 1);
lean_inc(v_numParams_3764_);
v_levelParams_3765_ = lean_ctor_get(v_toConstantVal_3763_, 1);
v_type_3766_ = lean_ctor_get(v_toConstantVal_3763_, 2);
lean_inc_ref(v_type_3766_);
v___x_3767_ = lean_box(0);
lean_inc(v_levelParams_3765_);
v_levels_3768_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3765_, v___x_3767_);
v___x_3777_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3778_ = lean_array_get_size(v_infos_3754_);
v___x_3779_ = lean_nat_dec_lt(v___x_3761_, v___x_3778_);
if (v___x_3779_ == 0)
{
v___y_3770_ = v___x_3777_;
goto v___jp_3769_;
}
else
{
size_t v___x_3780_; size_t v___x_3781_; lean_object* v___x_3782_; 
v___x_3780_ = ((size_t)0ULL);
v___x_3781_ = lean_usize_of_nat(v___x_3778_);
v___x_3782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3754_, v___x_3780_, v___x_3781_, v___x_3777_);
v___y_3770_ = v___x_3782_;
goto v___jp_3769_;
}
v___jp_3769_:
{
lean_object* v___f_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; lean_object* v___x_3776_; 
lean_inc_ref(v_infos_3754_);
v___f_3771_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3771_, 0, v_infos_3754_);
lean_closure_set(v___f_3771_, 1, v_levels_3768_);
lean_closure_set(v___f_3771_, 2, v___y_3770_);
v___x_3772_ = lean_array_get_size(v_infos_3754_);
lean_dec_ref(v_infos_3754_);
v___x_3773_ = lean_nat_sub(v_numParams_3764_, v___x_3772_);
lean_dec(v_numParams_3764_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
v___x_3775_ = 0;
v___x_3776_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_3766_, v___x_3774_, v___f_3771_, v___x_3775_, v___x_3775_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_);
return v___x_3776_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_0interp(lean_interpreter_value* stack)
{
lean_object* v_infos_3754_ = stack[0].m_obj;
lean_object* v_a_3755_ = stack[1].m_obj;
lean_object* v_a_3756_ = stack[2].m_obj;
lean_object* v_a_3757_ = stack[3].m_obj;
lean_object* v_a_3758_ = stack[4].m_obj;
lean_object* v_res_3783_;
v_res_3783_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_);
stack->m_obj
 = v_res_3783_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
return v_res_3790_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3791_, lean_object* v_constName_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_3792_ = stack[1].m_obj;
lean_object* v___y_3793_ = stack[2].m_obj;
lean_object* v___y_3794_ = stack[3].m_obj;
lean_object* v___y_3795_ = stack[4].m_obj;
lean_object* v___y_3796_ = stack[5].m_obj;
lean_object* v_res_3799_;
v_res_3799_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_box(0), v_constName_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
stack->m_obj
 = v_res_3799_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3800_, lean_object* v_constName_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3800_, v_constName_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3807_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3808_, lean_object* v_ref_3809_, lean_object* v_constName_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3809_, v_constName_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
return v___x_3816_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3809_ = stack[1].m_obj;
lean_object* v_constName_3810_ = stack[2].m_obj;
lean_object* v___y_3811_ = stack[3].m_obj;
lean_object* v___y_3812_ = stack[4].m_obj;
lean_object* v___y_3813_ = stack[5].m_obj;
lean_object* v___y_3814_ = stack[6].m_obj;
lean_object* v_res_3817_;
v_res_3817_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_box(0), v_ref_3809_, v_constName_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
stack->m_obj
 = v_res_3817_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3818_, lean_object* v_ref_3819_, lean_object* v_constName_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3818_, v_ref_3819_, v_constName_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v_ref_3819_);
return v_res_3826_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3827_, lean_object* v_ref_3828_, lean_object* v_msg_3829_, lean_object* v_declHint_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3828_, v_msg_3829_, v_declHint_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3836_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3828_ = stack[1].m_obj;
lean_object* v_msg_3829_ = stack[2].m_obj;
lean_object* v_declHint_3830_ = stack[3].m_obj;
lean_object* v___y_3831_ = stack[4].m_obj;
lean_object* v___y_3832_ = stack[5].m_obj;
lean_object* v___y_3833_ = stack[6].m_obj;
lean_object* v___y_3834_ = stack[7].m_obj;
lean_object* v_res_3837_;
v_res_3837_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_box(0), v_ref_3828_, v_msg_3829_, v_declHint_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
stack->m_obj
 = v_res_3837_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3838_, lean_object* v_ref_3839_, lean_object* v_msg_3840_, lean_object* v_declHint_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v_res_3847_; 
v_res_3847_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3838_, v_ref_3839_, v_msg_3840_, v_declHint_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v_ref_3839_);
return v_res_3847_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3848_, lean_object* v_declHint_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3848_, v_declHint_3849_, v___y_3853_);
return v___x_3855_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3848_ = stack[0].m_obj;
lean_object* v_declHint_3849_ = stack[1].m_obj;
lean_object* v___y_3850_ = stack[2].m_obj;
lean_object* v___y_3851_ = stack[3].m_obj;
lean_object* v___y_3852_ = stack[4].m_obj;
lean_object* v___y_3853_ = stack[5].m_obj;
lean_object* v_res_3856_;
v_res_3856_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3848_, v_declHint_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
stack->m_obj
 = v_res_3856_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3857_, lean_object* v_declHint_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3857_, v_declHint_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
return v_res_3864_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3865_, lean_object* v_ref_3866_, lean_object* v_msg_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3866_, v_msg_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3866_ = stack[1].m_obj;
lean_object* v_msg_3867_ = stack[2].m_obj;
lean_object* v___y_3868_ = stack[3].m_obj;
lean_object* v___y_3869_ = stack[4].m_obj;
lean_object* v___y_3870_ = stack[5].m_obj;
lean_object* v___y_3871_ = stack[6].m_obj;
lean_object* v_res_3874_;
v_res_3874_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_box(0), v_ref_3866_, v_msg_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
stack->m_obj
 = v_res_3874_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3875_, lean_object* v_ref_3876_, lean_object* v_msg_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3875_, v_ref_3876_, v_msg_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v_ref_3876_);
return v_res_3883_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3887_, lean_object* v___x_3888_, lean_object* v_params_3889_, size_t v_sz_3890_, size_t v_i_3891_, lean_object* v_bs_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
uint8_t v___x_3898_; 
v___x_3898_ = lean_usize_dec_lt(v_i_3891_, v_sz_3890_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; 
lean_dec_ref(v_params_3889_);
lean_dec_ref(v___x_3888_);
lean_dec(v___x_3887_);
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v_bs_3892_);
return v___x_3899_;
}
else
{
lean_object* v_v_3900_; lean_object* v_toConstantVal_3901_; lean_object* v_name_3902_; lean_object* v___x_3903_; lean_object* v_bs_x27_3904_; lean_object* v___y_3906_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_v_3900_ = lean_array_uget_borrowed(v_bs_3892_, v_i_3891_);
v_toConstantVal_3901_ = lean_ctor_get(v_v_3900_, 0);
v_name_3902_ = lean_ctor_get(v_toConstantVal_3901_, 0);
lean_inc(v_name_3902_);
v___x_3903_ = lean_unsigned_to_nat(0u);
v_bs_x27_3904_ = lean_array_uset(v_bs_3892_, v_i_3891_, v___x_3903_);
v___x_3920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3921_ = l_Lean_Name_append(v_name_3902_, v___x_3920_);
lean_inc(v___x_3887_);
v___x_3922_ = l_Lean_mkConst(v___x_3921_, v___x_3887_);
v___x_3923_ = l_Lean_Meta_unfoldDefinition(v___x_3922_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; size_t v_sz_3925_; size_t v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; uint8_t v___x_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v_sz_3925_ = lean_array_size(v___x_3888_);
v___x_3926_ = ((size_t)0ULL);
lean_inc_ref(v___x_3888_);
v___x_3927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3889_, v_sz_3925_, v___x_3926_, v___x_3888_);
lean_inc_ref(v_params_3889_);
v___x_3928_ = l_Array_append___redArg(v_params_3889_, v___x_3927_);
lean_dec_ref(v___x_3927_);
v___x_3929_ = l_Lean_mkAppN(v_a_3924_, v___x_3928_);
lean_dec_ref(v___x_3928_);
v___x_3930_ = 0;
v___x_3931_ = 1;
v___x_3932_ = l_Lean_Meta_mkLambdaFVars(v_params_3889_, v___x_3929_, v___x_3930_, v___x_3898_, v___x_3930_, v___x_3898_, v___x_3931_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
v___y_3906_ = v___x_3932_;
goto v___jp_3905_;
}
else
{
v___y_3906_ = v___x_3923_;
goto v___jp_3905_;
}
v___jp_3905_:
{
if (lean_obj_tag(v___y_3906_) == 0)
{
lean_object* v_a_3907_; size_t v___x_3908_; size_t v___x_3909_; lean_object* v___x_3910_; 
v_a_3907_ = lean_ctor_get(v___y_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___y_3906_, 1);
v___x_3908_ = ((size_t)1ULL);
v___x_3909_ = lean_usize_add(v_i_3891_, v___x_3908_);
v___x_3910_ = lean_array_uset(v_bs_x27_3904_, v_i_3891_, v_a_3907_);
v_i_3891_ = v___x_3909_;
v_bs_3892_ = v___x_3910_;
goto _start;
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v_bs_x27_3904_);
lean_dec_ref(v_params_3889_);
lean_dec_ref(v___x_3888_);
lean_dec(v___x_3887_);
v_a_3912_ = lean_ctor_get(v___y_3906_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___y_3906_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___y_3906_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___y_3906_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3887_ = stack[0].m_obj;
lean_object* v___x_3888_ = stack[1].m_obj;
lean_object* v_params_3889_ = stack[2].m_obj;
size_t v_sz_3890_ = stack[3].m_num;
size_t v_i_3891_ = stack[4].m_num;
lean_object* v_bs_3892_ = stack[5].m_obj;
lean_object* v___y_3893_ = stack[6].m_obj;
lean_object* v___y_3894_ = stack[7].m_obj;
lean_object* v___y_3895_ = stack[8].m_obj;
lean_object* v___y_3896_ = stack[9].m_obj;
lean_object* v_res_3933_;
v_res_3933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3887_, v___x_3888_, v_params_3889_, v_sz_3890_, v_i_3891_, v_bs_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
stack->m_obj
 = v_res_3933_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3934_, lean_object* v___x_3935_, lean_object* v_params_3936_, lean_object* v_sz_3937_, lean_object* v_i_3938_, lean_object* v_bs_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3937_);
lean_dec(v_sz_3937_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3934_, v___x_3935_, v_params_3936_, v_sz_boxed_3945_, v_i_boxed_3946_, v_bs_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
return v_res_3947_;
}
}
lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3948_, lean_object* v___x_3949_, size_t v_sz_3950_, size_t v___x_3951_, lean_object* v_a_3952_, lean_object* v_params_3953_, lean_object* v_x_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3948_, v___x_3949_, v_params_3953_, v_sz_3950_, v___x_3951_, v_a_3952_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabCoinductive___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3948_ = stack[0].m_obj;
lean_object* v___x_3949_ = stack[1].m_obj;
size_t v_sz_3950_ = stack[2].m_num;
size_t v___x_3951_ = stack[3].m_num;
lean_object* v_a_3952_ = stack[4].m_obj;
lean_object* v_params_3953_ = stack[5].m_obj;
lean_object* v_x_3954_ = stack[6].m_obj;
lean_object* v___y_3955_ = stack[7].m_obj;
lean_object* v___y_3956_ = stack[8].m_obj;
lean_object* v___y_3957_ = stack[9].m_obj;
lean_object* v___y_3958_ = stack[10].m_obj;
lean_object* v___y_3959_ = stack[11].m_obj;
lean_object* v___y_3960_ = stack[12].m_obj;
lean_object* v_res_3963_;
v_res_3963_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3948_, v___x_3949_, v_sz_3950_, v___x_3951_, v_a_3952_, v_params_3953_, v_x_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_);
stack->m_obj
 = v_res_3963_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3964_, lean_object* v___x_3965_, lean_object* v_sz_3966_, lean_object* v___x_3967_, lean_object* v_a_3968_, lean_object* v_params_3969_, lean_object* v_x_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
size_t v_sz_boxed_3978_; size_t v___x_5796__boxed_3979_; lean_object* v_res_3980_; 
v_sz_boxed_3978_ = lean_unbox_usize(v_sz_3966_);
lean_dec(v_sz_3966_);
v___x_5796__boxed_3979_ = lean_unbox_usize(v___x_3967_);
lean_dec(v___x_3967_);
v_res_3980_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3964_, v___x_3965_, v_sz_boxed_3978_, v___x_5796__boxed_3979_, v_a_3968_, v_params_3969_, v_x_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec_ref(v_x_3970_);
return v_res_3980_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(lean_object* v___x_3981_, uint8_t v___x_3982_, lean_object* v_attr_3983_){
_start:
{
lean_object* v_name_3984_; lean_object* v___x_3985_; 
v_name_3984_ = lean_ctor_get(v_attr_3983_, 0);
lean_inc(v_name_3984_);
lean_dec_ref(v_attr_3983_);
v___x_3985_ = l_Lean_getAttributeImpl(v___x_3981_, v_name_3984_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_dec_ref_known(v___x_3985_, 1);
return v___x_3982_;
}
else
{
lean_object* v_a_3986_; lean_object* v_toAttributeImplCore_3987_; uint8_t v_applicationTime_3988_; uint8_t v___x_3989_; uint8_t v___x_3990_; 
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref_known(v___x_3985_, 1);
v_toAttributeImplCore_3987_ = lean_ctor_get(v_a_3986_, 0);
lean_inc_ref(v_toAttributeImplCore_3987_);
lean_dec(v_a_3986_);
v_applicationTime_3988_ = lean_ctor_get_uint8(v_toAttributeImplCore_3987_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_3987_);
v___x_3989_ = 1;
v___x_3990_ = l_Lean_instBEqAttributeApplicationTime_beq(v_applicationTime_3988_, v___x_3989_);
if (v___x_3990_ == 0)
{
return v___x_3982_;
}
else
{
uint8_t v___x_3991_; 
v___x_3991_ = 0;
return v___x_3991_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3981_ = stack[0].m_obj;
uint8_t v___x_3982_ = stack[1].m_num;
lean_object* v_attr_3983_ = stack[2].m_obj;
uint8_t v_res_3992_;
v_res_3992_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(v___x_3981_, v___x_3982_, v_attr_3983_);
stack->m_num = v_res_3992_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed(lean_object* v___x_3993_, lean_object* v___x_3994_, lean_object* v_attr_3995_){
_start:
{
uint8_t v___x_5858__boxed_3996_; uint8_t v_res_3997_; lean_object* v_r_3998_; 
v___x_5858__boxed_3996_ = lean_unbox(v___x_3994_);
v_res_3997_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(v___x_3993_, v___x_5858__boxed_3996_, v_attr_3995_);
v_r_3998_ = lean_box(v_res_3997_);
return v_r_3998_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = l_Lean_instInhabitedExpr;
v___x_4000_ = lean_box(0);
v___x_4001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
lean_ctor_set(v___x_4001_, 1, v___x_3999_);
return v___x_4001_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_4002_, lean_object* v___x_4003_, lean_object* v_a_4004_, lean_object* v___x_4005_, size_t v_sz_4006_, size_t v_i_4007_, lean_object* v_bs_4008_){
_start:
{
uint8_t v___x_4009_; 
v___x_4009_ = lean_usize_dec_lt(v_i_4007_, v_sz_4006_);
if (v___x_4009_ == 0)
{
lean_dec(v___x_4005_);
lean_dec_ref(v___x_4003_);
return v_bs_4008_;
}
else
{
lean_object* v___x_4010_; lean_object* v_v_4011_; lean_object* v___x_4012_; lean_object* v_bs_x27_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v_modifiers_4016_; lean_object* v_ref_4017_; uint8_t v_isGreatest_4018_; lean_object* v_monotonicity_x3f_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4061_; 
v___x_4010_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v_v_4011_ = lean_array_uget(v_bs_4008_, v_i_4007_);
v___x_4012_ = lean_unsigned_to_nat(0u);
v_bs_x27_4013_ = lean_array_uset(v_bs_4008_, v_i_4007_, v___x_4012_);
v___x_4014_ = lean_usize_to_nat(v_i_4007_);
v___x_4015_ = lean_array_get(v___x_4010_, v_coinductiveElabData_4002_, v___x_4014_);
v_modifiers_4016_ = lean_ctor_get(v___x_4015_, 3);
v_ref_4017_ = lean_ctor_get(v___x_4015_, 2);
v_isGreatest_4018_ = lean_ctor_get_uint8(v___x_4015_, sizeof(void*)*6);
v_monotonicity_x3f_4019_ = lean_ctor_get(v___x_4015_, 5);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4061_ == 0)
{
lean_object* v_unused_4062_; lean_object* v_unused_4063_; lean_object* v_unused_4064_; 
v_unused_4062_ = lean_ctor_get(v___x_4015_, 4);
lean_dec(v_unused_4062_);
v_unused_4063_ = lean_ctor_get(v___x_4015_, 1);
lean_dec(v_unused_4063_);
v_unused_4064_ = lean_ctor_get(v___x_4015_, 0);
lean_dec(v_unused_4064_);
v___x_4021_ = v___x_4015_;
v_isShared_4022_ = v_isSharedCheck_4061_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_monotonicity_x3f_4019_);
lean_inc(v_modifiers_4016_);
lean_inc(v_ref_4017_);
lean_dec(v___x_4015_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4061_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v_stx_4023_; uint8_t v_visibility_4024_; uint8_t v_isProtected_4025_; uint8_t v_computeKind_4026_; uint8_t v_recKind_4027_; uint8_t v_isUnsafe_4028_; lean_object* v_attrs_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4059_; 
v_stx_4023_ = lean_ctor_get(v_modifiers_4016_, 0);
v_visibility_4024_ = lean_ctor_get_uint8(v_modifiers_4016_, sizeof(void*)*3);
v_isProtected_4025_ = lean_ctor_get_uint8(v_modifiers_4016_, sizeof(void*)*3 + 1);
v_computeKind_4026_ = lean_ctor_get_uint8(v_modifiers_4016_, sizeof(void*)*3 + 2);
v_recKind_4027_ = lean_ctor_get_uint8(v_modifiers_4016_, sizeof(void*)*3 + 3);
v_isUnsafe_4028_ = lean_ctor_get_uint8(v_modifiers_4016_, sizeof(void*)*3 + 4);
v_attrs_4029_ = lean_ctor_get(v_modifiers_4016_, 2);
v_isSharedCheck_4059_ = !lean_is_exclusive(v_modifiers_4016_);
if (v_isSharedCheck_4059_ == 0)
{
lean_object* v_unused_4060_; 
v_unused_4060_ = lean_ctor_get(v_modifiers_4016_, 1);
lean_dec(v_unused_4060_);
v___x_4031_ = v_modifiers_4016_;
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_attrs_4029_);
lean_inc(v_stx_4023_);
lean_dec(v_modifiers_4016_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4059_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v_fst_4035_; lean_object* v_snd_4036_; lean_object* v___x_4037_; lean_object* v___f_4038_; lean_object* v___x_4039_; lean_object* v___x_4041_; 
v___x_4033_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_4034_ = lean_array_get_borrowed(v___x_4033_, v_a_4004_, v___x_4014_);
lean_dec(v___x_4014_);
v_fst_4035_ = lean_ctor_get(v___x_4034_, 0);
v_snd_4036_ = lean_ctor_get(v___x_4034_, 1);
v___x_4037_ = lean_box(v___x_4009_);
lean_inc_ref(v___x_4003_);
v___f_4038_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4038_, 0, v___x_4003_);
lean_closure_set(v___f_4038_, 1, v___x_4037_);
v___x_4039_ = lean_box(0);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 1, v___x_4039_);
v___x_4041_ = v___x_4031_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_stx_4023_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4058_, 2, v_attrs_4029_);
lean_ctor_set_uint8(v_reuseFailAlloc_4058_, sizeof(void*)*3, v_visibility_4024_);
lean_ctor_set_uint8(v_reuseFailAlloc_4058_, sizeof(void*)*3 + 1, v_isProtected_4025_);
lean_ctor_set_uint8(v_reuseFailAlloc_4058_, sizeof(void*)*3 + 2, v_computeKind_4026_);
lean_ctor_set_uint8(v_reuseFailAlloc_4058_, sizeof(void*)*3 + 3, v_recKind_4027_);
lean_ctor_set_uint8(v_reuseFailAlloc_4058_, sizeof(void*)*3 + 4, v_isUnsafe_4028_);
v___x_4041_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
lean_object* v___x_4042_; uint8_t v___x_4043_; uint8_t v___y_4045_; 
v___x_4042_ = l_Lean_Elab_Modifiers_filterAttrs(v___x_4041_, v___f_4038_);
v___x_4043_ = 0;
if (v_isGreatest_4018_ == 0)
{
uint8_t v___x_4056_; 
v___x_4056_ = 2;
v___y_4045_ = v___x_4056_;
goto v___jp_4044_;
}
else
{
uint8_t v___x_4057_; 
v___x_4057_ = 1;
v___y_4045_ = v___x_4057_;
goto v___jp_4044_;
}
v___jp_4044_:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4049_; 
lean_inc_n(v_ref_4017_, 2);
v___x_4046_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4046_, 0, v_ref_4017_);
lean_ctor_set(v___x_4046_, 1, v_monotonicity_x3f_4019_);
lean_ctor_set_uint8(v___x_4046_, sizeof(void*)*2, v___y_4045_);
v___x_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 5, v___x_4012_);
lean_ctor_set(v___x_4021_, 4, v___x_4039_);
lean_ctor_set(v___x_4021_, 3, v___x_4047_);
lean_ctor_set(v___x_4021_, 2, v___x_4039_);
lean_ctor_set(v___x_4021_, 1, v___x_4039_);
lean_ctor_set(v___x_4021_, 0, v_ref_4017_);
v___x_4049_ = v___x_4021_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_ref_4017_);
lean_ctor_set(v_reuseFailAlloc_4055_, 1, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4055_, 2, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4055_, 3, v___x_4047_);
lean_ctor_set(v_reuseFailAlloc_4055_, 4, v___x_4039_);
lean_ctor_set(v_reuseFailAlloc_4055_, 5, v___x_4012_);
v___x_4049_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
lean_object* v___x_4050_; size_t v___x_4051_; size_t v___x_4052_; lean_object* v___x_4053_; 
lean_ctor_set_uint8(v___x_4049_, sizeof(void*)*6, v___x_4009_);
lean_inc(v_snd_4036_);
lean_inc(v_fst_4035_);
lean_inc(v___x_4005_);
lean_inc(v_ref_4017_);
v___x_4050_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_4050_, 0, v_ref_4017_);
lean_ctor_set(v___x_4050_, 1, v___x_4005_);
lean_ctor_set(v___x_4050_, 2, v___x_4042_);
lean_ctor_set(v___x_4050_, 3, v_fst_4035_);
lean_ctor_set(v___x_4050_, 4, v_ref_4017_);
lean_ctor_set(v___x_4050_, 5, v___x_4012_);
lean_ctor_set(v___x_4050_, 6, v_snd_4036_);
lean_ctor_set(v___x_4050_, 7, v_v_4011_);
lean_ctor_set(v___x_4050_, 8, v___x_4049_);
lean_ctor_set_uint8(v___x_4050_, sizeof(void*)*9, v___x_4043_);
v___x_4051_ = ((size_t)1ULL);
v___x_4052_ = lean_usize_add(v_i_4007_, v___x_4051_);
v___x_4053_ = lean_array_uset(v_bs_x27_4013_, v_i_4007_, v___x_4050_);
v_i_4007_ = v___x_4052_;
v_bs_4008_ = v___x_4053_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_coinductiveElabData_4002_ = stack[0].m_obj;
lean_object* v___x_4003_ = stack[1].m_obj;
lean_object* v_a_4004_ = stack[2].m_obj;
lean_object* v___x_4005_ = stack[3].m_obj;
size_t v_sz_4006_ = stack[4].m_num;
size_t v_i_4007_ = stack[5].m_num;
lean_object* v_bs_4008_ = stack[6].m_obj;
lean_object* v_res_4065_;
v_res_4065_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4002_, v___x_4003_, v_a_4004_, v___x_4005_, v_sz_4006_, v_i_4007_, v_bs_4008_);
stack->m_obj
 = v_res_4065_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object* v_coinductiveElabData_4066_, lean_object* v___x_4067_, lean_object* v_a_4068_, lean_object* v___x_4069_, lean_object* v_sz_4070_, lean_object* v_i_4071_, lean_object* v_bs_4072_){
_start:
{
size_t v_sz_boxed_4073_; size_t v_i_boxed_4074_; lean_object* v_res_4075_; 
v_sz_boxed_4073_ = lean_unbox_usize(v_sz_4070_);
lean_dec(v_sz_4070_);
v_i_boxed_4074_ = lean_unbox_usize(v_i_4071_);
lean_dec(v_i_4071_);
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4066_, v___x_4067_, v_a_4068_, v___x_4069_, v_sz_boxed_4073_, v_i_boxed_4074_, v_bs_4072_);
lean_dec_ref(v_a_4068_);
lean_dec_ref(v_coinductiveElabData_4066_);
return v_res_4075_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object* v_constName_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v___x_4087_; lean_object* v_env_4088_; lean_object* v___x_4089_; 
v___x_4087_ = lean_st_ref_get(v___y_4085_);
v_env_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc_ref(v_env_4088_);
lean_dec(v___x_4087_);
lean_inc(v_constName_4079_);
v___x_4089_ = l_Lean_isInductiveCore_x3f(v_env_4088_, v_constName_4079_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v___x_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4090_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_4091_ = 0;
v___x_4092_ = l_Lean_MessageData_ofConstName(v_constName_4079_, v___x_4091_);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4090_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
v___x_4095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4093_);
lean_ctor_set(v___x_4095_, 1, v___x_4094_);
v___x_4096_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_4095_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
return v___x_4096_;
}
else
{
lean_object* v_val_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_constName_4079_);
v_val_4097_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4089_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_val_4097_);
lean_dec(v___x_4089_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
lean_ctor_set_tag(v___x_4099_, 0);
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_val_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_4079_ = stack[0].m_obj;
lean_object* v___y_4080_ = stack[1].m_obj;
lean_object* v___y_4081_ = stack[2].m_obj;
lean_object* v___y_4082_ = stack[3].m_obj;
lean_object* v___y_4083_ = stack[4].m_obj;
lean_object* v___y_4084_ = stack[5].m_obj;
lean_object* v___y_4085_ = stack[6].m_obj;
lean_object* v_res_4105_;
v_res_4105_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
stack->m_obj
 = v_res_4105_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object* v_constName_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
return v_res_4114_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t v_sz_4115_, size_t v_i_4116_, lean_object* v_bs_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
uint8_t v___x_4125_; 
v___x_4125_ = lean_usize_dec_lt(v_i_4116_, v_sz_4115_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4126_; 
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v_bs_4117_);
return v___x_4126_;
}
else
{
lean_object* v_v_4127_; lean_object* v_declName_4128_; lean_object* v___x_4129_; lean_object* v_bs_x27_4130_; lean_object* v___x_4131_; 
v_v_4127_ = lean_array_uget_borrowed(v_bs_4117_, v_i_4116_);
v_declName_4128_ = lean_ctor_get(v_v_4127_, 1);
lean_inc(v_declName_4128_);
v___x_4129_ = lean_unsigned_to_nat(0u);
v_bs_x27_4130_ = lean_array_uset(v_bs_4117_, v_i_4116_, v___x_4129_);
v___x_4131_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_4128_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; size_t v___x_4133_; size_t v___x_4134_; lean_object* v___x_4135_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
v___x_4133_ = ((size_t)1ULL);
v___x_4134_ = lean_usize_add(v_i_4116_, v___x_4133_);
v___x_4135_ = lean_array_uset(v_bs_x27_4130_, v_i_4116_, v_a_4132_);
v_i_4116_ = v___x_4134_;
v_bs_4117_ = v___x_4135_;
goto _start;
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v_bs_x27_4130_);
v_a_4137_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4131_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4131_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4115_ = stack[0].m_num;
size_t v_i_4116_ = stack[1].m_num;
lean_object* v_bs_4117_ = stack[2].m_obj;
lean_object* v___y_4118_ = stack[3].m_obj;
lean_object* v___y_4119_ = stack[4].m_obj;
lean_object* v___y_4120_ = stack[5].m_obj;
lean_object* v___y_4121_ = stack[6].m_obj;
lean_object* v___y_4122_ = stack[7].m_obj;
lean_object* v___y_4123_ = stack[8].m_obj;
lean_object* v_res_4145_;
v_res_4145_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4115_, v_i_4116_, v_bs_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
stack->m_obj
 = v_res_4145_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object* v_sz_4146_, lean_object* v_i_4147_, lean_object* v_bs_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
size_t v_sz_boxed_4156_; size_t v_i_boxed_4157_; lean_object* v_res_4158_; 
v_sz_boxed_4156_ = lean_unbox_usize(v_sz_4146_);
lean_dec(v_sz_4146_);
v_i_boxed_4157_ = lean_unbox_usize(v_i_4147_);
lean_dec(v_i_4147_);
v_res_4158_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_4156_, v_i_boxed_4157_, v_bs_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
if (lean_obj_tag(v_a_4159_) == 0)
{
lean_object* v___x_4161_; 
v___x_4161_ = l_List_reverse___redArg(v_a_4160_);
return v___x_4161_;
}
else
{
lean_object* v_head_4162_; lean_object* v_tail_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4172_; 
v_head_4162_ = lean_ctor_get(v_a_4159_, 0);
v_tail_4163_ = lean_ctor_get(v_a_4159_, 1);
v_isSharedCheck_4172_ = !lean_is_exclusive(v_a_4159_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4165_ = v_a_4159_;
v_isShared_4166_ = v_isSharedCheck_4172_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_tail_4163_);
lean_inc(v_head_4162_);
lean_dec(v_a_4159_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4172_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4167_ = l_Lean_MessageData_ofName(v_head_4162_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 1, v_a_4160_);
lean_ctor_set(v___x_4165_, 0, v___x_4167_);
v___x_4169_ = v___x_4165_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4167_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v_a_4160_);
v___x_4169_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
v_a_4159_ = v_tail_4163_;
v_a_4160_ = v___x_4169_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t v_sz_4173_, size_t v_i_4174_, lean_object* v_bs_4175_){
_start:
{
uint8_t v___x_4176_; 
v___x_4176_ = lean_usize_dec_lt(v_i_4174_, v_sz_4173_);
if (v___x_4176_ == 0)
{
return v_bs_4175_;
}
else
{
lean_object* v_v_4177_; lean_object* v_declName_4178_; lean_object* v___x_4179_; lean_object* v_bs_x27_4180_; size_t v___x_4181_; size_t v___x_4182_; lean_object* v___x_4183_; 
v_v_4177_ = lean_array_uget_borrowed(v_bs_4175_, v_i_4174_);
v_declName_4178_ = lean_ctor_get(v_v_4177_, 1);
lean_inc(v_declName_4178_);
v___x_4179_ = lean_unsigned_to_nat(0u);
v_bs_x27_4180_ = lean_array_uset(v_bs_4175_, v_i_4174_, v___x_4179_);
v___x_4181_ = ((size_t)1ULL);
v___x_4182_ = lean_usize_add(v_i_4174_, v___x_4181_);
v___x_4183_ = lean_array_uset(v_bs_x27_4180_, v_i_4174_, v_declName_4178_);
v_i_4174_ = v___x_4182_;
v_bs_4175_ = v___x_4183_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4173_ = stack[0].m_num;
size_t v_i_4174_ = stack[1].m_num;
lean_object* v_bs_4175_ = stack[2].m_obj;
lean_object* v_res_4185_;
v_res_4185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4173_, v_i_4174_, v_bs_4175_);
stack->m_obj
 = v_res_4185_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object* v_sz_4186_, lean_object* v_i_4187_, lean_object* v_bs_4188_){
_start:
{
size_t v_sz_boxed_4189_; size_t v_i_boxed_4190_; lean_object* v_res_4191_; 
v_sz_boxed_4189_ = lean_unbox_usize(v_sz_4186_);
lean_dec(v_sz_4186_);
v_i_boxed_4190_ = lean_unbox_usize(v_i_4187_);
lean_dec(v_i_4187_);
v_res_4191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_4189_, v_i_boxed_4190_, v_bs_4188_);
return v_res_4191_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v_v_4192_, lean_object* v___x_4193_, lean_object* v___x_4194_, uint8_t v___x_4195_, lean_object* v_args_4196_, lean_object* v_body_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v_numParams_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; uint8_t v___x_4213_; lean_object* v___x_4214_; 
v_numParams_4205_ = lean_ctor_get(v_v_4192_, 1);
lean_inc(v_numParams_4205_);
lean_dec(v_v_4192_);
lean_inc_ref(v_args_4196_);
v___x_4206_ = l_Array_toSubarray___redArg(v_args_4196_, v___x_4193_, v___x_4194_);
v___x_4207_ = l_Subarray_copy___redArg(v___x_4206_);
v___x_4208_ = lean_array_get_size(v_args_4196_);
v___x_4209_ = l_Array_toSubarray___redArg(v_args_4196_, v_numParams_4205_, v___x_4208_);
v___x_4210_ = l_Subarray_copy___redArg(v___x_4209_);
v___x_4211_ = l_Array_append___redArg(v___x_4207_, v___x_4210_);
lean_dec_ref(v___x_4210_);
v___x_4212_ = 0;
v___x_4213_ = 1;
v___x_4214_ = l_Lean_Meta_mkForallFVars(v___x_4211_, v_body_4197_, v___x_4212_, v___x_4195_, v___x_4195_, v___x_4213_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec_ref(v___x_4211_);
return v___x_4214_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_4192_ = stack[0].m_obj;
lean_object* v___x_4193_ = stack[1].m_obj;
lean_object* v___x_4194_ = stack[2].m_obj;
uint8_t v___x_4195_ = stack[3].m_num;
lean_object* v_args_4196_ = stack[4].m_obj;
lean_object* v_body_4197_ = stack[5].m_obj;
lean_object* v___y_4198_ = stack[6].m_obj;
lean_object* v___y_4199_ = stack[7].m_obj;
lean_object* v___y_4200_ = stack[8].m_obj;
lean_object* v___y_4201_ = stack[9].m_obj;
lean_object* v___y_4202_ = stack[10].m_obj;
lean_object* v___y_4203_ = stack[11].m_obj;
lean_object* v_res_4215_;
v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_4192_, v___x_4193_, v___x_4194_, v___x_4195_, v_args_4196_, v_body_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
stack->m_obj
 = v_res_4215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v_v_4216_, lean_object* v___x_4217_, lean_object* v___x_4218_, lean_object* v___x_4219_, lean_object* v_args_4220_, lean_object* v_body_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
uint8_t v___x_6282__boxed_4229_; lean_object* v_res_4230_; 
v___x_6282__boxed_4229_ = lean_unbox(v___x_4219_);
v_res_4230_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_4216_, v___x_4217_, v___x_4218_, v___x_6282__boxed_4229_, v_args_4220_, v_body_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
return v_res_4230_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_4231_, size_t v_sz_4232_, size_t v_i_4233_, lean_object* v_bs_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
uint8_t v___x_4242_; 
v___x_4242_ = lean_usize_dec_lt(v_i_4233_, v_sz_4232_);
if (v___x_4242_ == 0)
{
lean_object* v___x_4243_; 
lean_dec(v___x_4231_);
v___x_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4243_, 0, v_bs_4234_);
return v___x_4243_;
}
else
{
lean_object* v_v_4244_; lean_object* v_toConstantVal_4245_; lean_object* v_name_4246_; lean_object* v_type_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___f_4250_; lean_object* v_bs_x27_4251_; uint8_t v___x_4252_; lean_object* v___x_4253_; 
v_v_4244_ = lean_array_uget_borrowed(v_bs_4234_, v_i_4233_);
v_toConstantVal_4245_ = lean_ctor_get(v_v_4244_, 0);
v_name_4246_ = lean_ctor_get(v_toConstantVal_4245_, 0);
lean_inc(v_name_4246_);
v_type_4247_ = lean_ctor_get(v_toConstantVal_4245_, 2);
lean_inc_ref(v_type_4247_);
v___x_4248_ = lean_unsigned_to_nat(0u);
v___x_4249_ = lean_box(v___x_4242_);
lean_inc(v___x_4231_);
lean_inc(v_v_4244_);
v___f_4250_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4250_, 0, v_v_4244_);
lean_closure_set(v___f_4250_, 1, v___x_4248_);
lean_closure_set(v___f_4250_, 2, v___x_4231_);
lean_closure_set(v___f_4250_, 3, v___x_4249_);
v_bs_x27_4251_ = lean_array_uset(v_bs_4234_, v_i_4233_, v___x_4248_);
v___x_4252_ = 0;
v___x_4253_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4247_, v___f_4250_, v___x_4252_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; size_t v___x_4257_; size_t v___x_4258_; lean_object* v___x_4259_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4246_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
lean_ctor_set(v___x_4256_, 1, v_a_4254_);
v___x_4257_ = ((size_t)1ULL);
v___x_4258_ = lean_usize_add(v_i_4233_, v___x_4257_);
v___x_4259_ = lean_array_uset(v_bs_x27_4251_, v_i_4233_, v___x_4256_);
v_i_4233_ = v___x_4258_;
v_bs_4234_ = v___x_4259_;
goto _start;
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec_ref(v_bs_x27_4251_);
lean_dec(v_name_4246_);
lean_dec(v___x_4231_);
v_a_4261_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4253_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4253_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4231_ = stack[0].m_obj;
size_t v_sz_4232_ = stack[1].m_num;
size_t v_i_4233_ = stack[2].m_num;
lean_object* v_bs_4234_ = stack[3].m_obj;
lean_object* v___y_4235_ = stack[4].m_obj;
lean_object* v___y_4236_ = stack[5].m_obj;
lean_object* v___y_4237_ = stack[6].m_obj;
lean_object* v___y_4238_ = stack[7].m_obj;
lean_object* v___y_4239_ = stack[8].m_obj;
lean_object* v___y_4240_ = stack[9].m_obj;
lean_object* v_res_4269_;
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4231_, v_sz_4232_, v_i_4233_, v_bs_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
stack->m_obj
 = v_res_4269_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object* v___x_4270_, lean_object* v_sz_4271_, lean_object* v_i_4272_, lean_object* v_bs_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
size_t v_sz_boxed_4281_; size_t v_i_boxed_4282_; lean_object* v_res_4283_; 
v_sz_boxed_4281_ = lean_unbox_usize(v_sz_4271_);
lean_dec(v_sz_4271_);
v_i_boxed_4282_ = lean_unbox_usize(v_i_4272_);
lean_dec(v_i_4272_);
v_res_4283_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4270_, v_sz_boxed_4281_, v_i_boxed_4282_, v_bs_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_);
lean_dec(v___y_4279_);
lean_dec_ref(v___y_4278_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
return v_res_4283_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object* v___x_4284_, size_t v_sz_4285_, size_t v_i_4286_, lean_object* v_bs_4287_){
_start:
{
uint8_t v___x_4288_; 
v___x_4288_ = lean_usize_dec_lt(v_i_4286_, v_sz_4285_);
if (v___x_4288_ == 0)
{
lean_dec(v___x_4284_);
return v_bs_4287_;
}
else
{
lean_object* v_v_4289_; lean_object* v_fst_4290_; lean_object* v___x_4291_; lean_object* v_bs_x27_4292_; lean_object* v___x_4293_; size_t v___x_4294_; size_t v___x_4295_; lean_object* v___x_4296_; 
v_v_4289_ = lean_array_uget_borrowed(v_bs_4287_, v_i_4286_);
v_fst_4290_ = lean_ctor_get(v_v_4289_, 0);
lean_inc(v_fst_4290_);
v___x_4291_ = lean_unsigned_to_nat(0u);
v_bs_x27_4292_ = lean_array_uset(v_bs_4287_, v_i_4286_, v___x_4291_);
lean_inc(v___x_4284_);
v___x_4293_ = l_Lean_mkConst(v_fst_4290_, v___x_4284_);
v___x_4294_ = ((size_t)1ULL);
v___x_4295_ = lean_usize_add(v_i_4286_, v___x_4294_);
v___x_4296_ = lean_array_uset(v_bs_x27_4292_, v_i_4286_, v___x_4293_);
v_i_4286_ = v___x_4295_;
v_bs_4287_ = v___x_4296_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4284_ = stack[0].m_obj;
size_t v_sz_4285_ = stack[1].m_num;
size_t v_i_4286_ = stack[2].m_num;
lean_object* v_bs_4287_ = stack[3].m_obj;
lean_object* v_res_4298_;
v_res_4298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4284_, v_sz_4285_, v_i_4286_, v_bs_4287_);
stack->m_obj
 = v_res_4298_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object* v___x_4299_, lean_object* v_sz_4300_, lean_object* v_i_4301_, lean_object* v_bs_4302_){
_start:
{
size_t v_sz_boxed_4303_; size_t v_i_boxed_4304_; lean_object* v_res_4305_; 
v_sz_boxed_4303_ = lean_unbox_usize(v_sz_4300_);
lean_dec(v_sz_4300_);
v_i_boxed_4304_ = lean_unbox_usize(v_i_4301_);
lean_dec(v_i_4301_);
v_res_4305_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4299_, v_sz_boxed_4303_, v_i_boxed_4304_, v_bs_4302_);
return v_res_4305_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCoinductive___closed__1(void){
_start:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = ((lean_object*)(l_Lean_Elab_Command_elabCoinductive___closed__0));
v___x_4308_ = l_Lean_stringToMessageData(v___x_4307_);
return v___x_4308_;
}
}
lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object* v_coinductiveElabData_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_toCold_4317_; lean_object* v_options_4318_; lean_object* v_inheritedTraceOptions_4319_; uint8_t v_hasTrace_4320_; lean_object* v___x_4321_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; 
v_toCold_4317_ = lean_ctor_get(v_a_4314_, 0);
v_options_4318_ = lean_ctor_get(v_toCold_4317_, 2);
v_inheritedTraceOptions_4319_ = lean_ctor_get(v_toCold_4317_, 11);
v_hasTrace_4320_ = lean_ctor_get_uint8(v_options_4318_, sizeof(void*)*1);
v___x_4321_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4320_ == 0)
{
v___y_4323_ = v_a_4310_;
v___y_4324_ = v_a_4311_;
v___y_4325_ = v_a_4312_;
v___y_4326_ = v_a_4313_;
v___y_4327_ = v_a_4314_;
v___y_4328_ = v_a_4315_;
goto v___jp_4322_;
}
else
{
lean_object* v_cls_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v_cls_4390_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4391_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4319_, v_options_4318_, v___x_4391_);
if (v___x_4392_ == 0)
{
v___y_4323_ = v_a_4310_;
v___y_4324_ = v_a_4311_;
v___y_4325_ = v_a_4312_;
v___y_4326_ = v_a_4313_;
v___y_4327_ = v_a_4314_;
v___y_4328_ = v_a_4315_;
goto v___jp_4322_;
}
else
{
lean_object* v___x_4393_; size_t v_sz_4394_; size_t v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4393_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4394_ = lean_array_size(v_coinductiveElabData_4309_);
v___x_4395_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4309_);
v___x_4396_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4394_, v___x_4395_, v_coinductiveElabData_4309_);
v___x_4397_ = lean_array_to_list(v___x_4396_);
v___x_4398_ = lean_box(0);
v___x_4399_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4397_, v___x_4398_);
v___x_4400_ = l_Lean_MessageData_ofList(v___x_4399_);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4393_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4390_, v___x_4401_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_dec_ref_known(v___x_4402_, 1);
v___y_4323_ = v_a_4310_;
v___y_4324_ = v_a_4311_;
v___y_4325_ = v_a_4312_;
v___y_4326_ = v_a_4313_;
v___y_4327_ = v_a_4314_;
v___y_4328_ = v_a_4315_;
goto v___jp_4322_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4309_);
return v___x_4402_;
}
}
}
v___jp_4322_:
{
size_t v_sz_4329_; size_t v___x_4330_; lean_object* v___x_4331_; 
v_sz_4329_ = lean_array_size(v_coinductiveElabData_4309_);
v___x_4330_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4309_);
v___x_4331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4329_, v___x_4330_, v_coinductiveElabData_4309_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4331_) == 0)
{
lean_object* v_a_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v_toConstantVal_4335_; lean_object* v_numParams_4336_; lean_object* v_levelParams_4337_; lean_object* v_type_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; size_t v_sz_4343_; lean_object* v___x_4344_; 
v_a_4332_ = lean_ctor_get(v___x_4331_, 0);
lean_inc_n(v_a_4332_, 2);
lean_dec_ref_known(v___x_4331_, 1);
v___x_4333_ = lean_unsigned_to_nat(0u);
v___x_4334_ = lean_array_get_borrowed(v___x_4321_, v_a_4332_, v___x_4333_);
v_toConstantVal_4335_ = lean_ctor_get(v___x_4334_, 0);
v_numParams_4336_ = lean_ctor_get(v___x_4334_, 1);
v_levelParams_4337_ = lean_ctor_get(v_toConstantVal_4335_, 1);
v_type_4338_ = lean_ctor_get(v_toConstantVal_4335_, 2);
v___x_4339_ = lean_box(0);
lean_inc(v_levelParams_4337_);
v___x_4340_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4337_, v___x_4339_);
v___x_4341_ = lean_array_get_size(v_a_4332_);
v___x_4342_ = lean_nat_sub(v_numParams_4336_, v___x_4341_);
v_sz_4343_ = lean_array_size(v_a_4332_);
lean_inc(v___x_4342_);
v___x_4344_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4342_, v_sz_4343_, v___x_4330_, v_a_4332_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; size_t v_sz_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___f_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; lean_object* v___x_4353_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc_n(v_a_4345_, 2);
lean_dec_ref_known(v___x_4344_, 1);
v_sz_4346_ = lean_array_size(v_a_4345_);
lean_inc(v___x_4340_);
v___x_4347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4340_, v_sz_4346_, v___x_4330_, v_a_4345_);
v___x_4348_ = lean_box_usize(v_sz_4343_);
v___x_4349_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4332_);
v___f_4350_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4350_, 0, v___x_4340_);
lean_closure_set(v___f_4350_, 1, v___x_4347_);
lean_closure_set(v___f_4350_, 2, v___x_4348_);
lean_closure_set(v___f_4350_, 3, v___x_4349_);
lean_closure_set(v___f_4350_, 4, v_a_4332_);
lean_inc(v___x_4342_);
v___x_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4342_);
v___x_4352_ = 0;
lean_inc_ref(v_type_4338_);
v___x_4353_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4338_, v___x_4351_, v___f_4350_, v___x_4352_, v___x_4352_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v_env_4356_; size_t v_sz_4357_; lean_object* v_lctx_4358_; lean_object* v_localInstances_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = lean_st_ref_get(v___y_4328_);
v_env_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc_ref(v_env_4356_);
lean_dec(v___x_4355_);
v_sz_4357_ = lean_array_size(v_a_4354_);
v_lctx_4358_ = lean_ctor_get(v___y_4325_, 2);
v_localInstances_4359_ = lean_ctor_get(v___y_4325_, 3);
lean_inc(v_levelParams_4337_);
v___x_4360_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4309_, v_env_4356_, v_a_4345_, v_levelParams_4337_, v_sz_4357_, v___x_4330_, v_a_4354_);
lean_dec(v_a_4345_);
lean_inc_ref(v_localInstances_4359_);
lean_inc_ref(v_lctx_4358_);
v___x_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4361_, 0, v_lctx_4358_);
lean_ctor_set(v___x_4361_, 1, v_localInstances_4359_);
v___x_4362_ = l_Lean_Elab_partialFixpoint(v___x_4361_, v___x_4360_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v___x_4363_; 
lean_dec_ref_known(v___x_4362_, 1);
lean_inc(v_a_4332_);
v___x_4363_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4332_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v___x_4364_; 
lean_dec_ref_known(v___x_4363_, 1);
lean_inc(v_a_4332_);
v___x_4364_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4342_, v_a_4332_, v_coinductiveElabData_4309_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v___x_4365_; 
lean_dec_ref_known(v___x_4364_, 1);
v___x_4365_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4332_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4365_;
}
else
{
lean_dec(v_a_4332_);
return v___x_4364_;
}
}
else
{
lean_dec(v___x_4342_);
lean_dec(v_a_4332_);
lean_dec_ref(v_coinductiveElabData_4309_);
return v___x_4363_;
}
}
else
{
lean_dec(v___x_4342_);
lean_dec(v_a_4332_);
lean_dec_ref(v_coinductiveElabData_4309_);
return v___x_4362_;
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v_a_4345_);
lean_dec(v___x_4342_);
lean_dec(v_a_4332_);
lean_dec_ref(v_coinductiveElabData_4309_);
v_a_4366_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4353_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4353_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
lean_dec(v___x_4342_);
lean_dec(v___x_4340_);
lean_dec(v_a_4332_);
lean_dec_ref(v_coinductiveElabData_4309_);
v_a_4374_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4344_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4344_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec_ref(v_coinductiveElabData_4309_);
v_a_4382_ = lean_ctor_get(v___x_4331_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4331_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4331_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4331_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Command_elabCoinductive_0interp(lean_interpreter_value* stack)
{
lean_object* v_coinductiveElabData_4309_ = stack[0].m_obj;
lean_object* v_a_4310_ = stack[1].m_obj;
lean_object* v_a_4311_ = stack[2].m_obj;
lean_object* v_a_4312_ = stack[3].m_obj;
lean_object* v_a_4313_ = stack[4].m_obj;
lean_object* v_a_4314_ = stack[5].m_obj;
lean_object* v_a_4315_ = stack[6].m_obj;
lean_object* v_res_4403_;
v_res_4403_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_);
stack->m_obj
 = v_res_4403_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4404_, v_a_4405_, v_a_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_a_4408_);
lean_dec_ref(v_a_4407_);
lean_dec(v_a_4406_);
lean_dec_ref(v_a_4405_);
return v_res_4412_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4413_, lean_object* v___x_4414_, lean_object* v_params_4415_, size_t v_sz_4416_, size_t v_i_4417_, lean_object* v_bs_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4413_, v___x_4414_, v_params_4415_, v_sz_4416_, v_i_4417_, v_bs_4418_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4413_ = stack[0].m_obj;
lean_object* v___x_4414_ = stack[1].m_obj;
lean_object* v_params_4415_ = stack[2].m_obj;
size_t v_sz_4416_ = stack[3].m_num;
size_t v_i_4417_ = stack[4].m_num;
lean_object* v_bs_4418_ = stack[5].m_obj;
lean_object* v___y_4419_ = stack[6].m_obj;
lean_object* v___y_4420_ = stack[7].m_obj;
lean_object* v___y_4421_ = stack[8].m_obj;
lean_object* v___y_4422_ = stack[9].m_obj;
lean_object* v___y_4423_ = stack[10].m_obj;
lean_object* v___y_4424_ = stack[11].m_obj;
lean_object* v_res_4427_;
v_res_4427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4413_, v___x_4414_, v_params_4415_, v_sz_4416_, v_i_4417_, v_bs_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
stack->m_obj
 = v_res_4427_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4428_, lean_object* v___x_4429_, lean_object* v_params_4430_, lean_object* v_sz_4431_, lean_object* v_i_4432_, lean_object* v_bs_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
size_t v_sz_boxed_4441_; size_t v_i_boxed_4442_; lean_object* v_res_4443_; 
v_sz_boxed_4441_ = lean_unbox_usize(v_sz_4431_);
lean_dec(v_sz_4431_);
v_i_boxed_4442_ = lean_unbox_usize(v_i_4432_);
lean_dec(v_i_4432_);
v_res_4443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4428_, v___x_4429_, v_params_4430_, v_sz_boxed_4441_, v_i_boxed_4442_, v_bs_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
return v_res_4443_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4444_, lean_object* v___x_4445_, lean_object* v_a_4446_, lean_object* v___x_4447_, lean_object* v_as_4448_, size_t v_sz_4449_, size_t v_i_4450_, lean_object* v_bs_4451_){
_start:
{
lean_object* v___x_4452_; 
v___x_4452_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4444_, v___x_4445_, v_a_4446_, v___x_4447_, v_sz_4449_, v_i_4450_, v_bs_4451_);
return v___x_4452_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_coinductiveElabData_4444_ = stack[0].m_obj;
lean_object* v___x_4445_ = stack[1].m_obj;
lean_object* v_a_4446_ = stack[2].m_obj;
lean_object* v___x_4447_ = stack[3].m_obj;
lean_object* v_as_4448_ = stack[4].m_obj;
size_t v_sz_4449_ = stack[5].m_num;
size_t v_i_4450_ = stack[6].m_num;
lean_object* v_bs_4451_ = stack[7].m_obj;
lean_object* v_res_4453_;
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4444_, v___x_4445_, v_a_4446_, v___x_4447_, v_as_4448_, v_sz_4449_, v_i_4450_, v_bs_4451_);
stack->m_obj
 = v_res_4453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4454_, lean_object* v___x_4455_, lean_object* v_a_4456_, lean_object* v___x_4457_, lean_object* v_as_4458_, lean_object* v_sz_4459_, lean_object* v_i_4460_, lean_object* v_bs_4461_){
_start:
{
size_t v_sz_boxed_4462_; size_t v_i_boxed_4463_; lean_object* v_res_4464_; 
v_sz_boxed_4462_ = lean_unbox_usize(v_sz_4459_);
lean_dec(v_sz_4459_);
v_i_boxed_4463_ = lean_unbox_usize(v_i_4460_);
lean_dec(v_i_4460_);
v_res_4464_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4454_, v___x_4455_, v_a_4456_, v___x_4457_, v_as_4458_, v_sz_boxed_4462_, v_i_boxed_4463_, v_bs_4461_);
lean_dec_ref(v_as_4458_);
lean_dec_ref(v_a_4456_);
lean_dec_ref(v_coinductiveElabData_4454_);
return v_res_4464_;
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
