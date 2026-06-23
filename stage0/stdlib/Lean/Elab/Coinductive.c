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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
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
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
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
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedModifiers_default;
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Elab_partialFixpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "` is not an inductive type"};
static const lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_74_ = 0;
v___x_75_ = ((lean_object*)(l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__0));
v___x_76_ = l_Lean_Elab_instInhabitedModifiers_default;
v___x_77_ = lean_box(0);
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_78_);
lean_ctor_set(v___x_79_, 3, v___x_76_);
lean_ctor_set(v___x_79_, 4, v___x_75_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*5, v___x_74_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default(void){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1, &l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1_once, _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default___closed__1);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_Elab_Command_instInhabitedCoinductiveElabData(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_addFunctorPostfix(lean_object* v_x_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = ((lean_object*)(l_Lean_Elab_Command_addFunctorPostfix___closed__1));
v___x_87_ = l_Lean_Name_append(v_x_85_, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfix(lean_object* v_x_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = l_Lean_Name_hasMacroScopes(v_x_88_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_Name_getPrefix(v_x_88_);
lean_dec(v_x_88_);
return v___x_90_;
}
else
{
lean_object* v_view_91_; lean_object* v_name_92_; lean_object* v_imported_93_; lean_object* v_ctx_94_; lean_object* v_scopes_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_104_; 
v_view_91_ = l_Lean_extractMacroScopes(v_x_88_);
v_name_92_ = lean_ctor_get(v_view_91_, 0);
v_imported_93_ = lean_ctor_get(v_view_91_, 1);
v_ctx_94_ = lean_ctor_get(v_view_91_, 2);
v_scopes_95_ = lean_ctor_get(v_view_91_, 3);
v_isSharedCheck_104_ = !lean_is_exclusive(v_view_91_);
if (v_isSharedCheck_104_ == 0)
{
v___x_97_ = v_view_91_;
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_scopes_95_);
lean_inc(v_ctx_94_);
lean_inc(v_imported_93_);
lean_inc(v_name_92_);
lean_dec(v_view_91_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_104_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_101_; 
v___x_99_ = l_Lean_Name_getPrefix(v_name_92_);
lean_dec(v_name_92_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_99_);
v___x_101_ = v___x_97_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_99_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_imported_93_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_ctx_94_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_scopes_95_);
v___x_101_ = v_reuseFailAlloc_103_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_MacroScopesView_review(v___x_101_);
return v___x_102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(lean_object* v_msg_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_box(0);
v___x_107_ = lean_panic_fn_borrowed(v___x_106_, v_msg_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_111_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__2));
v___x_112_ = lean_unsigned_to_nat(13u);
v___x_113_ = lean_unsigned_to_nat(124u);
v___x_114_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__1));
v___x_115_ = ((lean_object*)(l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__0));
v___x_116_ = l_mkPanicMessageWithDecl(v___x_115_, v___x_114_, v___x_113_, v___x_112_, v___x_111_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_removeFunctorPostfixInCtor(lean_object* v_x_117_){
_start:
{
if (lean_obj_tag(v_x_117_) == 1)
{
lean_object* v_pre_118_; lean_object* v_str_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_pre_118_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_pre_118_);
v_str_119_ = lean_ctor_get(v_x_117_, 1);
lean_inc_ref(v_str_119_);
lean_dec_ref_known(v_x_117_, 2);
v___x_120_ = l_Lean_Elab_Command_removeFunctorPostfix(v_pre_118_);
v___x_121_ = l_Lean_Name_str___override(v___x_120_, v_str_119_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec(v_x_117_);
v___x_122_ = lean_obj_once(&l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3, &l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3_once, _init_l_Lean_Elab_Command_removeFunctorPostfixInCtor___closed__3);
v___x_123_ = l_panic___at___00Lean_Elab_Command_removeFunctorPostfixInCtor_spec__0(v___x_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(lean_object* v_goal_129_, lean_object* v_eq_130_, uint8_t v_symm_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
lean_inc(v_goal_129_);
v___x_137_ = l_Lean_MVarId_getType(v_goal_129_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v_goal_129_);
v___x_140_ = l_Lean_MVarId_rewrite(v_goal_129_, v_a_138_, v_eq_130_, v_symm_131_, v___x_139_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v_eNew_142_; lean_object* v_eqProof_143_; lean_object* v___x_144_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v_eNew_142_ = lean_ctor_get(v_a_141_, 0);
lean_inc_ref(v_eNew_142_);
v_eqProof_143_ = lean_ctor_get(v_a_141_, 1);
lean_inc_ref(v_eqProof_143_);
lean_dec(v_a_141_);
v___x_144_ = l_Lean_MVarId_replaceTargetEq(v_goal_129_, v_eNew_142_, v_eqProof_143_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
return v___x_144_;
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_goal_129_);
v_a_145_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_140_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_140_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec_ref(v_eq_130_);
lean_dec(v_goal_129_);
v_a_153_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_137_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_137_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___boxed(lean_object* v_goal_161_, lean_object* v_eq_162_, lean_object* v_symm_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
uint8_t v_symm_boxed_169_; lean_object* v_res_170_; 
v_symm_boxed_169_ = lean_unbox(v_symm_163_);
v_res_170_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v_goal_161_, v_eq_162_, v_symm_boxed_169_, v_a_164_, v_a_165_, v_a_166_, v_a_167_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(lean_object* v_e_171_, lean_object* v___y_172_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_Expr_hasMVar(v_e_171_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_175_, 0, v_e_171_);
return v___x_175_;
}
else
{
lean_object* v___x_176_; lean_object* v_mctx_177_; lean_object* v___x_178_; lean_object* v_fst_179_; lean_object* v_snd_180_; lean_object* v___x_181_; lean_object* v_cache_182_; lean_object* v_zetaDeltaFVarIds_183_; lean_object* v_postponed_184_; lean_object* v_diag_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_194_; 
v___x_176_ = lean_st_ref_get(v___y_172_);
v_mctx_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc_ref(v_mctx_177_);
lean_dec(v___x_176_);
v___x_178_ = l_Lean_instantiateMVarsCore(v_mctx_177_, v_e_171_);
v_fst_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_fst_179_);
v_snd_180_ = lean_ctor_get(v___x_178_, 1);
lean_inc(v_snd_180_);
lean_dec_ref(v___x_178_);
v___x_181_ = lean_st_ref_take(v___y_172_);
v_cache_182_ = lean_ctor_get(v___x_181_, 1);
v_zetaDeltaFVarIds_183_ = lean_ctor_get(v___x_181_, 2);
v_postponed_184_ = lean_ctor_get(v___x_181_, 3);
v_diag_185_ = lean_ctor_get(v___x_181_, 4);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_194_ == 0)
{
lean_object* v_unused_195_; 
v_unused_195_ = lean_ctor_get(v___x_181_, 0);
lean_dec(v_unused_195_);
v___x_187_ = v___x_181_;
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_diag_185_);
lean_inc(v_postponed_184_);
lean_inc(v_zetaDeltaFVarIds_183_);
lean_inc(v_cache_182_);
lean_dec(v___x_181_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_194_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v_snd_180_);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_snd_180_);
lean_ctor_set(v_reuseFailAlloc_193_, 1, v_cache_182_);
lean_ctor_set(v_reuseFailAlloc_193_, 2, v_zetaDeltaFVarIds_183_);
lean_ctor_set(v_reuseFailAlloc_193_, 3, v_postponed_184_);
lean_ctor_set(v_reuseFailAlloc_193_, 4, v_diag_185_);
v___x_190_ = v_reuseFailAlloc_193_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = lean_st_ref_set(v___y_172_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_fst_179_);
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg___boxed(lean_object* v_e_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_196_, v___y_197_);
lean_dec(v___y_197_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(lean_object* v_e_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_e_200_, v___y_202_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___boxed(lean_object* v_e_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5(v_e_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(lean_object* v_k_214_, lean_object* v_b_215_, lean_object* v_c_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
lean_inc(v___y_218_);
lean_inc_ref(v___y_217_);
v___x_222_ = lean_apply_7(v_k_214_, v_b_215_, v_c_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, lean_box(0));
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed(lean_object* v_k_223_, lean_object* v_b_224_, lean_object* v_c_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0(v_k_223_, v_b_224_, v_c_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(lean_object* v_type_232_, lean_object* v_k_233_, uint8_t v_cleanupAnnotations_234_, uint8_t v_whnfType_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___f_241_; lean_object* v___x_242_; 
v___f_241_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_241_, 0, v_k_233_);
v___x_242_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_232_, v___f_241_, v_cleanupAnnotations_234_, v_whnfType_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_242_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_242_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_a_251_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_242_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_242_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___boxed(lean_object* v_type_259_, lean_object* v_k_260_, lean_object* v_cleanupAnnotations_261_, lean_object* v_whnfType_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_268_; uint8_t v_whnfType_boxed_269_; lean_object* v_res_270_; 
v_cleanupAnnotations_boxed_268_ = lean_unbox(v_cleanupAnnotations_261_);
v_whnfType_boxed_269_ = lean_unbox(v_whnfType_262_);
v_res_270_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_259_, v_k_260_, v_cleanupAnnotations_boxed_268_, v_whnfType_boxed_269_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(lean_object* v_00_u03b1_271_, lean_object* v_type_272_, lean_object* v_k_273_, uint8_t v_cleanupAnnotations_274_, uint8_t v_whnfType_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_272_, v_k_273_, v_cleanupAnnotations_274_, v_whnfType_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___boxed(lean_object* v_00_u03b1_282_, lean_object* v_type_283_, lean_object* v_k_284_, lean_object* v_cleanupAnnotations_285_, lean_object* v_whnfType_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_292_; uint8_t v_whnfType_boxed_293_; lean_object* v_res_294_; 
v_cleanupAnnotations_boxed_292_ = lean_unbox(v_cleanupAnnotations_285_);
v_whnfType_boxed_293_ = lean_unbox(v_whnfType_286_);
v_res_294_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6(v_00_u03b1_282_, v_type_283_, v_k_284_, v_cleanupAnnotations_boxed_292_, v_whnfType_boxed_293_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(lean_object* v_name_295_, lean_object* v_levelParams_296_, lean_object* v_type_297_, lean_object* v_value_298_, lean_object* v_hints_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; uint8_t v___y_304_; uint8_t v___y_311_; lean_object* v_env_314_; uint8_t v___x_315_; 
v___x_302_ = lean_st_ref_get(v___y_300_);
v_env_314_ = lean_ctor_get(v___x_302_, 0);
lean_inc_ref_n(v_env_314_, 2);
lean_dec(v___x_302_);
v___x_315_ = l_Lean_Environment_hasUnsafe(v_env_314_, v_type_297_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = l_Lean_Environment_hasUnsafe(v_env_314_, v_value_298_);
v___y_311_ = v___x_316_;
goto v___jp_310_;
}
else
{
lean_dec_ref(v_env_314_);
v___y_311_ = v___x_315_;
goto v___jp_310_;
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_inc(v_name_295_);
v___x_305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_305_, 0, v_name_295_);
lean_ctor_set(v___x_305_, 1, v_levelParams_296_);
lean_ctor_set(v___x_305_, 2, v_type_297_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_307_, 0, v_name_295_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_308_, 0, v___x_305_);
lean_ctor_set(v___x_308_, 1, v_value_298_);
lean_ctor_set(v___x_308_, 2, v_hints_299_);
lean_ctor_set(v___x_308_, 3, v___x_307_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*4, v___y_304_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
v___jp_310_:
{
if (v___y_311_ == 0)
{
uint8_t v___x_312_; 
v___x_312_ = 1;
v___y_304_ = v___x_312_;
goto v___jp_303_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = 0;
v___y_304_ = v___x_313_;
goto v___jp_303_;
}
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
v___x_396_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_448_; lean_object* v_vs_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_469_; 
v_ks_448_ = lean_ctor_get(v_x_397_, 0);
v_vs_449_ = lean_ctor_get(v_x_397_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_x_397_);
if (v_isSharedCheck_469_ == 0)
{
v___x_451_ = v_x_397_;
v_isShared_452_ = v_isSharedCheck_469_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_vs_449_);
lean_inc(v_ks_448_);
lean_dec(v_x_397_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_469_;
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
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_ks_448_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_vs_449_);
v___x_454_ = v_reuseFailAlloc_468_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v_newNode_455_; uint8_t v___y_457_; size_t v___x_463_; uint8_t v___x_464_; 
v_newNode_455_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v___x_454_, v_x_400_, v_x_401_);
v___x_463_ = ((size_t)7ULL);
v___x_464_ = lean_usize_dec_le(v___x_463_, v_x_399_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_455_);
v___x_466_ = lean_unsigned_to_nat(4u);
v___x_467_ = lean_nat_dec_lt(v___x_465_, v___x_466_);
lean_dec(v___x_465_);
v___y_457_ = v___x_467_;
goto v___jp_456_;
}
else
{
v___y_457_ = v___x_464_;
goto v___jp_456_;
}
v___jp_456_:
{
if (v___y_457_ == 0)
{
lean_object* v_ks_458_; lean_object* v_vs_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_ks_458_ = lean_ctor_get(v_newNode_455_, 0);
lean_inc_ref(v_ks_458_);
v_vs_459_ = lean_ctor_get(v_newNode_455_, 1);
lean_inc_ref(v_vs_459_);
lean_dec_ref(v_newNode_455_);
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0);
v___x_462_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_x_399_, v_ks_458_, v_vs_459_, v___x_460_, v___x_461_);
lean_dec_ref(v_vs_459_);
lean_dec_ref(v_ks_458_);
return v___x_462_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(size_t v_depth_470_, lean_object* v_keys_471_, lean_object* v_vals_472_, lean_object* v_i_473_, lean_object* v_entries_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_array_get_size(v_keys_471_);
v___x_476_ = lean_nat_dec_lt(v_i_473_, v___x_475_);
if (v___x_476_ == 0)
{
lean_dec(v_i_473_);
return v_entries_474_;
}
else
{
lean_object* v_k_477_; lean_object* v_v_478_; uint64_t v___x_479_; size_t v_h_480_; size_t v___x_481_; lean_object* v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v_h_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_k_477_ = lean_array_fget_borrowed(v_keys_471_, v_i_473_);
v_v_478_ = lean_array_fget_borrowed(v_vals_472_, v_i_473_);
v___x_479_ = l_Lean_instHashableMVarId_hash(v_k_477_);
v_h_480_ = lean_uint64_to_usize(v___x_479_);
v___x_481_ = ((size_t)5ULL);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v_depth_470_, v___x_483_);
v___x_485_ = lean_usize_mul(v___x_481_, v___x_484_);
v_h_486_ = lean_usize_shift_right(v_h_480_, v___x_485_);
v___x_487_ = lean_nat_add(v_i_473_, v___x_482_);
lean_dec(v_i_473_);
lean_inc(v_v_478_);
lean_inc(v_k_477_);
v___x_488_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_entries_474_, v_h_486_, v_depth_470_, v_k_477_, v_v_478_);
v_i_473_ = v___x_487_;
v_entries_474_ = v___x_488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_depth_490_, lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_i_493_, lean_object* v_entries_494_){
_start:
{
size_t v_depth_boxed_495_; lean_object* v_res_496_; 
v_depth_boxed_495_ = lean_unbox_usize(v_depth_490_);
lean_dec(v_depth_490_);
v_res_496_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_boxed_495_, v_keys_491_, v_vals_492_, v_i_493_, v_entries_494_);
lean_dec_ref(v_vals_492_);
lean_dec_ref(v_keys_491_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
size_t v_x_8767__boxed_502_; size_t v_x_8768__boxed_503_; lean_object* v_res_504_; 
v_x_8767__boxed_502_ = lean_unbox_usize(v_x_498_);
lean_dec(v_x_498_);
v_x_8768__boxed_503_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_res_504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_497_, v_x_8767__boxed_502_, v_x_8768__boxed_503_, v_x_500_, v_x_501_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
uint64_t v___x_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_508_ = l_Lean_instHashableMVarId_hash(v_x_506_);
v___x_509_ = lean_uint64_to_usize(v___x_508_);
v___x_510_ = ((size_t)1ULL);
v___x_511_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_505_, v___x_509_, v___x_510_, v_x_506_, v_x_507_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object* v_mvarId_512_, lean_object* v_val_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; lean_object* v_mctx_517_; lean_object* v_cache_518_; lean_object* v_zetaDeltaFVarIds_519_; lean_object* v_postponed_520_; lean_object* v_diag_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_549_; 
v___x_516_ = lean_st_ref_take(v___y_514_);
v_mctx_517_ = lean_ctor_get(v___x_516_, 0);
v_cache_518_ = lean_ctor_get(v___x_516_, 1);
v_zetaDeltaFVarIds_519_ = lean_ctor_get(v___x_516_, 2);
v_postponed_520_ = lean_ctor_get(v___x_516_, 3);
v_diag_521_ = lean_ctor_get(v___x_516_, 4);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_549_ == 0)
{
v___x_523_ = v___x_516_;
v_isShared_524_ = v_isSharedCheck_549_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_diag_521_);
lean_inc(v_postponed_520_);
lean_inc(v_zetaDeltaFVarIds_519_);
lean_inc(v_cache_518_);
lean_inc(v_mctx_517_);
lean_dec(v___x_516_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_549_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_depth_525_; lean_object* v_levelAssignDepth_526_; lean_object* v_lmvarCounter_527_; lean_object* v_mvarCounter_528_; lean_object* v_lDecls_529_; lean_object* v_decls_530_; lean_object* v_userNames_531_; lean_object* v_lAssignment_532_; lean_object* v_eAssignment_533_; lean_object* v_dAssignment_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_548_; 
v_depth_525_ = lean_ctor_get(v_mctx_517_, 0);
v_levelAssignDepth_526_ = lean_ctor_get(v_mctx_517_, 1);
v_lmvarCounter_527_ = lean_ctor_get(v_mctx_517_, 2);
v_mvarCounter_528_ = lean_ctor_get(v_mctx_517_, 3);
v_lDecls_529_ = lean_ctor_get(v_mctx_517_, 4);
v_decls_530_ = lean_ctor_get(v_mctx_517_, 5);
v_userNames_531_ = lean_ctor_get(v_mctx_517_, 6);
v_lAssignment_532_ = lean_ctor_get(v_mctx_517_, 7);
v_eAssignment_533_ = lean_ctor_get(v_mctx_517_, 8);
v_dAssignment_534_ = lean_ctor_get(v_mctx_517_, 9);
v_isSharedCheck_548_ = !lean_is_exclusive(v_mctx_517_);
if (v_isSharedCheck_548_ == 0)
{
v___x_536_ = v_mctx_517_;
v_isShared_537_ = v_isSharedCheck_548_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_dAssignment_534_);
lean_inc(v_eAssignment_533_);
lean_inc(v_lAssignment_532_);
lean_inc(v_userNames_531_);
lean_inc(v_decls_530_);
lean_inc(v_lDecls_529_);
lean_inc(v_mvarCounter_528_);
lean_inc(v_lmvarCounter_527_);
lean_inc(v_levelAssignDepth_526_);
lean_inc(v_depth_525_);
lean_dec(v_mctx_517_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_548_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_538_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_533_, v_mvarId_512_, v_val_513_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 8, v___x_538_);
v___x_540_ = v___x_536_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_depth_525_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_levelAssignDepth_526_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_lmvarCounter_527_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_mvarCounter_528_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_lDecls_529_);
lean_ctor_set(v_reuseFailAlloc_547_, 5, v_decls_530_);
lean_ctor_set(v_reuseFailAlloc_547_, 6, v_userNames_531_);
lean_ctor_set(v_reuseFailAlloc_547_, 7, v_lAssignment_532_);
lean_ctor_set(v_reuseFailAlloc_547_, 8, v___x_538_);
lean_ctor_set(v_reuseFailAlloc_547_, 9, v_dAssignment_534_);
v___x_540_ = v_reuseFailAlloc_547_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_542_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_540_);
v___x_542_ = v___x_523_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_540_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_cache_518_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_zetaDeltaFVarIds_519_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_postponed_520_);
lean_ctor_set(v_reuseFailAlloc_546_, 4, v_diag_521_);
v___x_542_ = v_reuseFailAlloc_546_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_543_ = lean_st_ref_set(v___y_514_, v___x_542_);
v___x_544_ = lean_box(0);
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
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
lean_object* v___x_561_; lean_object* v_env_562_; lean_object* v___x_563_; lean_object* v_mctx_564_; lean_object* v_lctx_565_; lean_object* v_options_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_561_ = lean_st_ref_get(v___y_559_);
v_env_562_ = lean_ctor_get(v___x_561_, 0);
lean_inc_ref(v_env_562_);
lean_dec(v___x_561_);
v___x_563_ = lean_st_ref_get(v___y_557_);
v_mctx_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc_ref(v_mctx_564_);
lean_dec(v___x_563_);
v_lctx_565_ = lean_ctor_get(v___y_556_, 2);
v_options_566_ = lean_ctor_get(v___y_558_, 2);
lean_inc_ref(v_options_566_);
lean_inc_ref(v_lctx_565_);
v___x_567_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_567_, 0, v_env_562_);
lean_ctor_set(v___x_567_, 1, v_mctx_564_);
lean_ctor_set(v___x_567_, 2, v_lctx_565_);
lean_ctor_set(v___x_567_, 3, v_options_566_);
v___x_568_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v_msgData_555_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_ref_583_; lean_object* v___x_584_; lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_593_; 
v_ref_583_ = lean_ctor_get(v___y_580_, 5);
v___x_584_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
v_a_585_ = lean_ctor_get(v___x_584_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_584_);
if (v_isSharedCheck_593_ == 0)
{
v___x_587_ = v___x_584_;
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_584_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_593_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_591_; 
lean_inc(v_ref_583_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_ref_583_);
lean_ctor_set(v___x_589_, 1, v_a_585_);
if (v_isShared_588_ == 0)
{
lean_ctor_set_tag(v___x_587_, 1);
lean_ctor_set(v___x_587_, 0, v___x_589_);
v___x_591_ = v___x_587_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v___x_589_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
lean_dec(v___y_598_);
lean_dec_ref(v___y_597_);
lean_dec(v___y_596_);
lean_dec_ref(v___y_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_601_, lean_object* v_b_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_array_608_; lean_object* v_start_609_; lean_object* v_stop_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_625_; 
v_array_608_ = lean_ctor_get(v_a_601_, 0);
v_start_609_ = lean_ctor_get(v_a_601_, 1);
v_stop_610_ = lean_ctor_get(v_a_601_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_601_);
if (v_isSharedCheck_625_ == 0)
{
v___x_612_ = v_a_601_;
v_isShared_613_ = v_isSharedCheck_625_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_stop_610_);
lean_inc(v_start_609_);
lean_inc(v_array_608_);
lean_dec(v_a_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_625_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
uint8_t v___x_614_; 
v___x_614_ = lean_nat_dec_lt(v_start_609_, v_stop_610_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; 
lean_del_object(v___x_612_);
lean_dec(v_stop_610_);
lean_dec(v_start_609_);
lean_dec_ref(v_array_608_);
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_b_602_);
return v___x_615_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_array_fget_borrowed(v_array_608_, v_start_609_);
lean_inc(v___x_616_);
v___x_617_ = l_Lean_Meta_mkCongrFun(v_b_602_, v___x_616_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_add(v_start_609_, v___x_619_);
lean_dec(v_start_609_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 1, v___x_620_);
v___x_622_ = v___x_612_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_array_608_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_stop_610_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
v_a_601_ = v___x_622_;
v_b_602_ = v_a_618_;
goto _start;
}
}
else
{
lean_del_object(v___x_612_);
lean_dec(v_stop_610_);
lean_dec(v_start_609_);
lean_dec_ref(v_array_608_);
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_626_, lean_object* v_b_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_626_, v_b_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_634_, lean_object* v___x_635_, size_t v_sz_636_, size_t v_i_637_, lean_object* v_bs_638_){
_start:
{
uint8_t v___x_639_; 
v___x_639_ = lean_usize_dec_lt(v_i_637_, v_sz_636_);
if (v___x_639_ == 0)
{
lean_dec(v_levels_634_);
return v_bs_638_;
}
else
{
lean_object* v_v_640_; lean_object* v_toConstantVal_641_; lean_object* v_name_642_; lean_object* v___x_643_; lean_object* v_bs_x27_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; size_t v___x_648_; size_t v___x_649_; lean_object* v___x_650_; 
v_v_640_ = lean_array_uget_borrowed(v_bs_638_, v_i_637_);
v_toConstantVal_641_ = lean_ctor_get(v_v_640_, 0);
v_name_642_ = lean_ctor_get(v_toConstantVal_641_, 0);
lean_inc(v_name_642_);
v___x_643_ = lean_unsigned_to_nat(0u);
v_bs_x27_644_ = lean_array_uset(v_bs_638_, v_i_637_, v___x_643_);
v___x_645_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_642_);
lean_inc(v_levels_634_);
v___x_646_ = l_Lean_mkConst(v___x_645_, v_levels_634_);
v___x_647_ = l_Lean_mkAppN(v___x_646_, v___x_635_);
v___x_648_ = ((size_t)1ULL);
v___x_649_ = lean_usize_add(v_i_637_, v___x_648_);
v___x_650_ = lean_array_uset(v_bs_x27_644_, v_i_637_, v___x_647_);
v_i_637_ = v___x_649_;
v_bs_638_ = v___x_650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_652_, lean_object* v___x_653_, lean_object* v_sz_654_, lean_object* v_i_655_, lean_object* v_bs_656_){
_start:
{
size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_sz_boxed_657_ = lean_unbox_usize(v_sz_654_);
lean_dec(v_sz_654_);
v_i_boxed_658_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_652_, v___x_653_, v_sz_boxed_657_, v_i_boxed_658_, v_bs_656_);
lean_dec_ref(v___x_653_);
return v_res_659_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0));
v___x_662_ = l_Lean_stringToMessageData(v___x_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object* v_infos_666_, lean_object* v_numParams_667_, lean_object* v___x_668_, lean_object* v_name_669_, lean_object* v_levels_670_, lean_object* v_args_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_678_ = lean_array_get_size(v_infos_666_);
v___x_679_ = lean_nat_sub(v_numParams_667_, v___x_678_);
lean_inc(v___x_668_);
lean_inc_ref(v_args_671_);
v___x_680_ = l_Array_toSubarray___redArg(v_args_671_, v___x_668_, v___x_679_);
v___x_681_ = lean_array_get_size(v_args_671_);
v___x_682_ = l_Array_toSubarray___redArg(v_args_671_, v_numParams_667_, v___x_681_);
lean_inc_n(v_name_669_, 2);
v___x_683_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_669_);
lean_inc_n(v_levels_670_, 3);
lean_inc(v___x_683_);
v___x_684_ = l_Lean_mkConst(v___x_683_, v_levels_670_);
v___x_685_ = l_Subarray_copy___redArg(v___x_680_);
v___x_686_ = l_Lean_mkAppN(v___x_684_, v___x_685_);
lean_inc_ref(v___x_682_);
v___x_687_ = l_Subarray_copy___redArg(v___x_682_);
v___x_688_ = l_Lean_mkAppN(v___x_686_, v___x_687_);
v_sz_689_ = lean_array_size(v_infos_666_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_670_, v___x_685_, v_sz_689_, v___x_690_, v_infos_666_);
v___x_692_ = l_Lean_mkConst(v_name_669_, v_levels_670_);
lean_inc_ref(v___x_685_);
v___x_693_ = l_Array_append___redArg(v___x_685_, v___x_691_);
lean_dec_ref(v___x_691_);
v___x_694_ = l_Array_append___redArg(v___x_693_, v___x_687_);
v___x_695_ = l_Lean_mkAppN(v___x_692_, v___x_694_);
lean_dec_ref(v___x_694_);
v___x_696_ = l_Lean_Meta_mkEq(v___x_688_, v___x_695_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_763_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_763_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_763_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_763_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 1);
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_762_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = 0;
v___x_704_ = lean_box(0);
v___x_705_ = l_Lean_Meta_mkFreshExprMVar(v___x_702_, v___x_703_, v___x_704_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v___x_707_ = l_Lean_Meta_getEqnsFor_x3f(v___x_683_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
if (lean_obj_tag(v_a_708_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_val_716_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_val_716_);
lean_dec_ref_known(v_a_708_, 1);
v___x_717_ = lean_array_get_size(v_val_716_);
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_dec_eq(v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
lean_dec(v_val_716_);
lean_dec(v_a_706_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec_ref(v___x_682_);
lean_dec(v_levels_670_);
lean_dec(v_name_669_);
lean_dec(v___x_668_);
v___y_710_ = v___y_673_;
v___y_711_ = v___y_674_;
v___y_712_ = v___y_675_;
v___y_713_ = v___y_676_;
goto v___jp_709_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_720_ = lean_array_fget(v_val_716_, v___x_668_);
lean_dec(v___x_668_);
lean_dec(v_val_716_);
v___x_721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3));
v___x_722_ = l_Lean_Name_append(v_name_669_, v___x_721_);
lean_inc(v_levels_670_);
v___x_723_ = l_Lean_mkConst(v___x_722_, v_levels_670_);
v___x_724_ = l_Lean_mkConst(v___x_720_, v_levels_670_);
v___x_725_ = l_Lean_mkAppN(v___x_724_, v___x_685_);
v___x_726_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_682_, v___x_725_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = l_Lean_Expr_mvarId_x21(v_a_706_);
v___x_729_ = 0;
v___x_730_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_728_, v___x_723_, v___x_729_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_731_, v_a_727_, v___y_674_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v___x_733_; 
lean_dec_ref_known(v___x_732_, 1);
v___x_733_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_706_, v___y_674_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; uint8_t v___x_736_; lean_object* v___x_737_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Array_append___redArg(v___x_685_, v___x_687_);
lean_dec_ref(v___x_687_);
v___x_736_ = 1;
v___x_737_ = l_Lean_Meta_mkLambdaFVars(v___x_735_, v_a_734_, v___x_729_, v___x_719_, v___x_729_, v___x_719_, v___x_736_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec_ref(v___x_735_);
return v___x_737_;
}
else
{
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
return v___x_733_;
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v_a_706_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
v_a_738_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_732_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_732_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_a_727_);
lean_dec(v_a_706_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
v_a_746_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_730_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_730_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_dec_ref(v___x_723_);
lean_dec(v_a_706_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
return v___x_726_;
}
}
}
else
{
lean_dec(v_a_708_);
lean_dec(v_a_706_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec_ref(v___x_682_);
lean_dec(v_levels_670_);
lean_dec(v_name_669_);
lean_dec(v___x_668_);
v___y_710_ = v___y_673_;
v___y_711_ = v___y_674_;
v___y_712_ = v___y_675_;
v___y_713_ = v___y_676_;
goto v___jp_709_;
}
v___jp_709_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
v___x_715_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_714_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
return v___x_715_;
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_706_);
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec_ref(v___x_682_);
lean_dec(v_levels_670_);
lean_dec(v_name_669_);
lean_dec(v___x_668_);
v_a_754_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_707_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_707_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v_levels_670_);
lean_dec(v_name_669_);
lean_dec(v___x_668_);
return v___x_705_;
}
}
}
}
else
{
lean_dec_ref(v___x_687_);
lean_dec_ref(v___x_685_);
lean_dec(v___x_683_);
lean_dec_ref(v___x_682_);
lean_dec(v_levels_670_);
lean_dec(v_name_669_);
lean_dec(v___x_668_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object* v_infos_764_, lean_object* v_numParams_765_, lean_object* v___x_766_, lean_object* v_name_767_, lean_object* v_levels_768_, lean_object* v_args_769_, lean_object* v_x_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_764_, v_numParams_765_, v___x_766_, v_name_767_, v_levels_768_, v_args_769_, v_x_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec_ref(v_x_770_);
return v_res_776_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0(void){
_start:
{
lean_object* v___x_777_; double v___x_778_; 
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_float_of_nat(v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_782_, lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_ref_789_; lean_object* v___x_790_; lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_835_; 
v_ref_789_ = lean_ctor_get(v___y_786_, 5);
v___x_790_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_835_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_835_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_835_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_795_; lean_object* v_traceState_796_; lean_object* v_env_797_; lean_object* v_nextMacroScope_798_; lean_object* v_ngen_799_; lean_object* v_auxDeclNGen_800_; lean_object* v_cache_801_; lean_object* v_messages_802_; lean_object* v_infoState_803_; lean_object* v_snapshotTasks_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_834_; 
v___x_795_ = lean_st_ref_take(v___y_787_);
v_traceState_796_ = lean_ctor_get(v___x_795_, 4);
v_env_797_ = lean_ctor_get(v___x_795_, 0);
v_nextMacroScope_798_ = lean_ctor_get(v___x_795_, 1);
v_ngen_799_ = lean_ctor_get(v___x_795_, 2);
v_auxDeclNGen_800_ = lean_ctor_get(v___x_795_, 3);
v_cache_801_ = lean_ctor_get(v___x_795_, 5);
v_messages_802_ = lean_ctor_get(v___x_795_, 6);
v_infoState_803_ = lean_ctor_get(v___x_795_, 7);
v_snapshotTasks_804_ = lean_ctor_get(v___x_795_, 8);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_834_ == 0)
{
v___x_806_ = v___x_795_;
v_isShared_807_ = v_isSharedCheck_834_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_snapshotTasks_804_);
lean_inc(v_infoState_803_);
lean_inc(v_messages_802_);
lean_inc(v_cache_801_);
lean_inc(v_traceState_796_);
lean_inc(v_auxDeclNGen_800_);
lean_inc(v_ngen_799_);
lean_inc(v_nextMacroScope_798_);
lean_inc(v_env_797_);
lean_dec(v___x_795_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_834_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint64_t v_tid_808_; lean_object* v_traces_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_833_; 
v_tid_808_ = lean_ctor_get_uint64(v_traceState_796_, sizeof(void*)*1);
v_traces_809_ = lean_ctor_get(v_traceState_796_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v_traceState_796_);
if (v_isSharedCheck_833_ == 0)
{
v___x_811_ = v_traceState_796_;
v_isShared_812_ = v_isSharedCheck_833_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_traces_809_);
lean_dec(v_traceState_796_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_833_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_813_; double v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_823_; 
v___x_813_ = lean_box(0);
v___x_814_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_815_ = 0;
v___x_816_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_817_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_817_, 0, v_cls_782_);
lean_ctor_set(v___x_817_, 1, v___x_813_);
lean_ctor_set(v___x_817_, 2, v___x_816_);
lean_ctor_set_float(v___x_817_, sizeof(void*)*3, v___x_814_);
lean_ctor_set_float(v___x_817_, sizeof(void*)*3 + 8, v___x_814_);
lean_ctor_set_uint8(v___x_817_, sizeof(void*)*3 + 16, v___x_815_);
v___x_818_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_819_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v_a_791_);
lean_ctor_set(v___x_819_, 2, v___x_818_);
lean_inc(v_ref_789_);
v___x_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_820_, 0, v_ref_789_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_PersistentArray_push___redArg(v_traces_809_, v___x_820_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_821_);
v___x_823_ = v___x_811_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_821_);
lean_ctor_set_uint64(v_reuseFailAlloc_832_, sizeof(void*)*1, v_tid_808_);
v___x_823_ = v_reuseFailAlloc_832_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
lean_object* v___x_825_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 4, v___x_823_);
v___x_825_ = v___x_806_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_env_797_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_nextMacroScope_798_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_ngen_799_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v_auxDeclNGen_800_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v___x_823_);
lean_ctor_set(v_reuseFailAlloc_831_, 5, v_cache_801_);
lean_ctor_set(v_reuseFailAlloc_831_, 6, v_messages_802_);
lean_ctor_set(v_reuseFailAlloc_831_, 7, v_infoState_803_);
lean_ctor_set(v_reuseFailAlloc_831_, 8, v_snapshotTasks_804_);
v___x_825_ = v_reuseFailAlloc_831_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_826_ = lean_st_ref_set(v___y_787_, v___x_825_);
v___x_827_ = lean_box(0);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_827_);
v___x_829_ = v___x_793_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object* v_cls_836_, lean_object* v_msg_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_836_, v_msg_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
return v_res_843_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_851_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_852_ = l_Lean_Name_append(v___x_851_, v___x_850_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object* v_infos_856_, lean_object* v_levels_857_, lean_object* v_as_858_, size_t v_sz_859_, size_t v_i_860_, lean_object* v_b_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_860_, v_sz_859_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
lean_dec(v_levels_857_);
lean_dec_ref(v_infos_856_);
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v_b_861_);
return v___x_868_;
}
else
{
lean_object* v_a_869_; lean_object* v_toConstantVal_870_; lean_object* v_numParams_871_; lean_object* v_name_872_; lean_object* v_levelParams_873_; lean_object* v_type_874_; lean_object* v___x_875_; lean_object* v___f_876_; uint8_t v___x_877_; lean_object* v___x_878_; 
v_a_869_ = lean_array_uget_borrowed(v_as_858_, v_i_860_);
v_toConstantVal_870_ = lean_ctor_get(v_a_869_, 0);
v_numParams_871_ = lean_ctor_get(v_a_869_, 1);
v_name_872_ = lean_ctor_get(v_toConstantVal_870_, 0);
v_levelParams_873_ = lean_ctor_get(v_toConstantVal_870_, 1);
v_type_874_ = lean_ctor_get(v_toConstantVal_870_, 2);
v___x_875_ = lean_unsigned_to_nat(0u);
lean_inc(v_levels_857_);
lean_inc(v_name_872_);
lean_inc(v_numParams_871_);
lean_inc_ref(v_infos_856_);
v___f_876_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed), 12, 5);
lean_closure_set(v___f_876_, 0, v_infos_856_);
lean_closure_set(v___f_876_, 1, v_numParams_871_);
lean_closure_set(v___f_876_, 2, v___x_875_);
lean_closure_set(v___f_876_, 3, v_name_872_);
lean_closure_set(v___f_876_, 4, v_levels_857_);
v___x_877_ = 0;
lean_inc_ref(v_type_874_);
v___x_878_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_874_, v___f_876_, v___x_877_, v___x_877_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_options_879_; lean_object* v_a_880_; lean_object* v_inheritedTraceOptions_881_; uint8_t v_hasTrace_882_; lean_object* v___x_883_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; 
v_options_879_ = lean_ctor_get(v___y_864_, 2);
v_a_880_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_878_, 1);
v_inheritedTraceOptions_881_ = lean_ctor_get(v___y_864_, 13);
v_hasTrace_882_ = lean_ctor_get_uint8(v_options_879_, sizeof(void*)*1);
v___x_883_ = lean_box(0);
if (v_hasTrace_882_ == 0)
{
v___y_885_ = v___y_862_;
v___y_886_ = v___y_863_;
v___y_887_ = v___y_864_;
v___y_888_ = v___y_865_;
goto v___jp_884_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_918_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_881_, v_options_879_, v___x_919_);
if (v___x_920_ == 0)
{
v___y_885_ = v___y_862_;
v___y_886_ = v___y_863_;
v___y_887_ = v___y_864_;
v___y_888_ = v___y_865_;
goto v___jp_884_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_921_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
lean_inc(v_a_880_);
v___x_922_ = l_Lean_MessageData_ofExpr(v_a_880_);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_918_, v___x_923_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_dec_ref_known(v___x_924_, 1);
v___y_885_ = v___y_862_;
v___y_886_ = v___y_863_;
v___y_887_ = v___y_864_;
v___y_888_ = v___y_865_;
goto v___jp_884_;
}
else
{
lean_dec(v_a_880_);
lean_dec(v_levels_857_);
lean_dec_ref(v_infos_856_);
return v___x_924_;
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
lean_inc(v_a_880_);
v___x_889_ = lean_infer_type(v_a_880_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
lean_inc(v_name_872_);
v___x_891_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_872_);
v___x_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_893_ = l_Lean_Name_append(v___x_891_, v___x_892_);
v___x_894_ = lean_box(0);
lean_inc(v_levelParams_873_);
v___x_895_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_893_, v_levelParams_873_, v_a_890_, v_a_880_, v___x_894_, v___y_888_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_897_, 0, v_a_896_);
v___x_898_ = l_Lean_addDecl(v___x_897_, v___x_877_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_898_) == 0)
{
size_t v___x_899_; size_t v___x_900_; 
lean_dec_ref_known(v___x_898_, 1);
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_860_, v___x_899_);
v_i_860_ = v___x_900_;
v_b_861_ = v___x_883_;
goto _start;
}
else
{
lean_dec(v_levels_857_);
lean_dec_ref(v_infos_856_);
return v___x_898_;
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_levels_857_);
lean_dec_ref(v_infos_856_);
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
lean_dec(v_a_880_);
lean_dec(v_levels_857_);
lean_dec_ref(v_infos_856_);
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
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec(v_levels_857_);
lean_dec_ref(v_infos_856_);
v_a_925_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_878_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_878_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object* v_infos_933_, lean_object* v_levels_934_, lean_object* v_as_935_, lean_object* v_sz_936_, lean_object* v_i_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
size_t v_sz_boxed_944_; size_t v_i_boxed_945_; lean_object* v_res_946_; 
v_sz_boxed_944_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_945_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_933_, v_levels_934_, v_as_935_, v_sz_boxed_944_, v_i_boxed_945_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec_ref(v_as_935_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object* v_infos_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v_toConstantVal_956_; lean_object* v_levelParams_957_; lean_object* v___x_958_; lean_object* v_levels_959_; lean_object* v___x_960_; size_t v_sz_961_; size_t v___x_962_; lean_object* v___x_963_; 
v___x_953_ = l_Lean_instInhabitedInductiveVal_default;
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_array_get_borrowed(v___x_953_, v_infos_947_, v___x_954_);
v_toConstantVal_956_ = lean_ctor_get(v___x_955_, 0);
v_levelParams_957_ = lean_ctor_get(v_toConstantVal_956_, 1);
v___x_958_ = lean_box(0);
lean_inc(v_levelParams_957_);
v_levels_959_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_957_, v___x_958_);
v___x_960_ = lean_box(0);
v_sz_961_ = lean_array_size(v_infos_947_);
v___x_962_ = ((size_t)0ULL);
lean_inc_ref(v_infos_947_);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_947_, v_levels_959_, v_infos_947_, v_sz_961_, v___x_962_, v___x_960_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec_ref(v_infos_947_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_970_; 
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v___x_963_, 0);
lean_dec(v_unused_971_);
v___x_965_ = v___x_963_;
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
else
{
lean_dec(v___x_963_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_970_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_968_; 
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_960_);
v___x_968_ = v___x_965_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_960_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
else
{
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object* v_infos_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object* v_00_u03b1_979_, lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object* v_00_u03b1_987_, lean_object* v_msg_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_987_, v_msg_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object* v_inst_995_, lean_object* v_R_996_, lean_object* v_a_997_, lean_object* v_b_998_, lean_object* v_c_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_997_, v_b_998_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object* v_inst_1006_, lean_object* v_R_1007_, lean_object* v_a_1008_, lean_object* v_b_1009_, lean_object* v_c_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_1006_, v_R_1007_, v_a_1008_, v_b_1009_, v_c_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object* v_mvarId_1017_, lean_object* v_val_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_1017_, v_val_1018_, v___y_1020_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object* v_mvarId_1025_, lean_object* v_val_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1025_, v_val_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_1034_, v_x_1035_, v_x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1038_, lean_object* v_x_1039_, size_t v_x_1040_, size_t v_x_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_1039_, v_x_1040_, v_x_1041_, v_x_1042_, v_x_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
size_t v_x_9695__boxed_1051_; size_t v_x_9696__boxed_1052_; lean_object* v_res_1053_; 
v_x_9695__boxed_1051_ = lean_unbox_usize(v_x_1047_);
lean_dec(v_x_1047_);
v_x_9696__boxed_1052_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_res_1053_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_1045_, v_x_1046_, v_x_9695__boxed_1051_, v_x_9696__boxed_1052_, v_x_1049_, v_x_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1054_, lean_object* v_n_1055_, lean_object* v_k_1056_, lean_object* v_v_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v_n_1055_, v_k_1056_, v_v_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1059_, size_t v_depth_1060_, lean_object* v_keys_1061_, lean_object* v_vals_1062_, lean_object* v_heq_1063_, lean_object* v_i_1064_, lean_object* v_entries_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_1060_, v_keys_1061_, v_vals_1062_, v_i_1064_, v_entries_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_depth_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_entries_1073_){
_start:
{
size_t v_depth_boxed_1074_; lean_object* v_res_1075_; 
v_depth_boxed_1074_ = lean_unbox_usize(v_depth_1068_);
lean_dec(v_depth_1068_);
v_res_1075_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(v_00_u03b2_1067_, v_depth_boxed_1074_, v_keys_1069_, v_vals_1070_, v_heq_1071_, v_i_1072_, v_entries_1073_);
lean_dec_ref(v_vals_1070_);
lean_dec_ref(v_keys_1069_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_x_1077_, v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object* v_e_1082_, lean_object* v___y_1083_){
_start:
{
uint8_t v___x_1085_; 
v___x_1085_ = l_Lean_Expr_hasMVar(v_e_1082_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v_e_1082_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; lean_object* v_mctx_1088_; lean_object* v___x_1089_; lean_object* v_fst_1090_; lean_object* v_snd_1091_; lean_object* v___x_1092_; lean_object* v_cache_1093_; lean_object* v_zetaDeltaFVarIds_1094_; lean_object* v_postponed_1095_; lean_object* v_diag_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1105_; 
v___x_1087_ = lean_st_ref_get(v___y_1083_);
v_mctx_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc_ref(v_mctx_1088_);
lean_dec(v___x_1087_);
v___x_1089_ = l_Lean_instantiateMVarsCore(v_mctx_1088_, v_e_1082_);
v_fst_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_fst_1090_);
v_snd_1091_ = lean_ctor_get(v___x_1089_, 1);
lean_inc(v_snd_1091_);
lean_dec_ref(v___x_1089_);
v___x_1092_ = lean_st_ref_take(v___y_1083_);
v_cache_1093_ = lean_ctor_get(v___x_1092_, 1);
v_zetaDeltaFVarIds_1094_ = lean_ctor_get(v___x_1092_, 2);
v_postponed_1095_ = lean_ctor_get(v___x_1092_, 3);
v_diag_1096_ = lean_ctor_get(v___x_1092_, 4);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v___x_1092_, 0);
lean_dec(v_unused_1106_);
v___x_1098_ = v___x_1092_;
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_diag_1096_);
lean_inc(v_postponed_1095_);
lean_inc(v_zetaDeltaFVarIds_1094_);
lean_inc(v_cache_1093_);
lean_dec(v___x_1092_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1101_; 
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v_snd_1091_);
v___x_1101_ = v___x_1098_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_snd_1091_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_cache_1093_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_zetaDeltaFVarIds_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_postponed_1095_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_diag_1096_);
v___x_1101_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_st_ref_set(v___y_1083_, v___x_1101_);
v___x_1103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1103_, 0, v_fst_1090_);
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_e_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1107_, v___y_1108_);
lean_dec(v___y_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_e_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1111_, v___y_1115_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_e_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object* v_k_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v_b_1132_, lean_object* v_c_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
lean_object* v___x_1139_; 
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1135_);
lean_inc_ref(v___y_1134_);
lean_inc(v___y_1131_);
lean_inc_ref(v___y_1130_);
v___x_1139_ = lean_apply_9(v_k_1129_, v_b_1132_, v_c_1133_, v___y_1130_, v___y_1131_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, lean_box(0));
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object* v_k_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v_b_1143_, lean_object* v_c_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1140_, v___y_1141_, v___y_1142_, v_b_1143_, v_c_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_type_1151_, lean_object* v_k_1152_, uint8_t v_cleanupAnnotations_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___f_1161_; uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
v___f_1161_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1161_, 0, v_k_1152_);
lean_closure_set(v___f_1161_, 1, v___y_1154_);
lean_closure_set(v___f_1161_, 2, v___y_1155_);
v___x_1162_ = 0;
v___x_1163_ = lean_box(0);
v___x_1164_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1162_, v___x_1163_, v_type_1151_, v___f_1161_, v_cleanupAnnotations_1153_, v___x_1162_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
if (lean_obj_tag(v___x_1164_) == 0)
{
return v___x_1164_;
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_type_1173_, lean_object* v_k_1174_, lean_object* v_cleanupAnnotations_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1183_; lean_object* v_res_1184_; 
v_cleanupAnnotations_boxed_1183_ = lean_unbox(v_cleanupAnnotations_1175_);
v_res_1184_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1173_, v_k_1174_, v_cleanupAnnotations_boxed_1183_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_00_u03b1_1185_, lean_object* v_type_1186_, lean_object* v_k_1187_, uint8_t v_cleanupAnnotations_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1186_, v_k_1187_, v_cleanupAnnotations_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_00_u03b1_1197_, lean_object* v_type_1198_, lean_object* v_k_1199_, lean_object* v_cleanupAnnotations_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1208_; lean_object* v_res_1209_; 
v_cleanupAnnotations_boxed_1208_ = lean_unbox(v_cleanupAnnotations_1200_);
v_res_1209_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_1197_, v_type_1198_, v_k_1199_, v_cleanupAnnotations_boxed_1208_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_name_1210_, lean_object* v_levelParams_1211_, lean_object* v_type_1212_, lean_object* v_value_1213_, lean_object* v_hints_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; uint8_t v___y_1219_; uint8_t v___y_1226_; lean_object* v_env_1229_; uint8_t v___x_1230_; 
v___x_1217_ = lean_st_ref_get(v___y_1215_);
v_env_1229_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref_n(v_env_1229_, 2);
lean_dec(v___x_1217_);
v___x_1230_ = l_Lean_Environment_hasUnsafe(v_env_1229_, v_type_1212_);
if (v___x_1230_ == 0)
{
uint8_t v___x_1231_; 
v___x_1231_ = l_Lean_Environment_hasUnsafe(v_env_1229_, v_value_1213_);
v___y_1226_ = v___x_1231_;
goto v___jp_1225_;
}
else
{
lean_dec_ref(v_env_1229_);
v___y_1226_ = v___x_1230_;
goto v___jp_1225_;
}
v___jp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_inc(v_name_1210_);
v___x_1220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1220_, 0, v_name_1210_);
lean_ctor_set(v___x_1220_, 1, v_levelParams_1211_);
lean_ctor_set(v___x_1220_, 2, v_type_1212_);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v_name_1210_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
v___x_1223_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1223_, 0, v___x_1220_);
lean_ctor_set(v___x_1223_, 1, v_value_1213_);
lean_ctor_set(v___x_1223_, 2, v_hints_1214_);
lean_ctor_set(v___x_1223_, 3, v___x_1222_);
lean_ctor_set_uint8(v___x_1223_, sizeof(void*)*4, v___y_1219_);
v___x_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
return v___x_1224_;
}
v___jp_1225_:
{
if (v___y_1226_ == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = 1;
v___y_1219_ = v___x_1227_;
goto v___jp_1218_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = 0;
v___y_1219_ = v___x_1228_;
goto v___jp_1218_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1232_, lean_object* v_levelParams_1233_, lean_object* v_type_1234_, lean_object* v_value_1235_, lean_object* v_hints_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1232_, v_levelParams_1233_, v_type_1234_, v_value_1235_, v_hints_1236_, v___y_1237_);
lean_dec(v___y_1237_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1240_, lean_object* v_levelParams_1241_, lean_object* v_type_1242_, lean_object* v_value_1243_, lean_object* v_hints_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1240_, v_levelParams_1241_, v_type_1242_, v_value_1243_, v_hints_1244_, v___y_1250_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1253_, lean_object* v_levelParams_1254_, lean_object* v_type_1255_, lean_object* v_value_1256_, lean_object* v_hints_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1253_, v_levelParams_1254_, v_type_1255_, v_value_1256_, v_hints_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1266_, lean_object* v_maxFVars_x3f_1267_, lean_object* v_k_1268_, uint8_t v_cleanupAnnotations_1269_, uint8_t v_whnfType_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___f_1278_; lean_object* v___x_1279_; 
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
v___f_1278_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1278_, 0, v_k_1268_);
lean_closure_set(v___f_1278_, 1, v___y_1271_);
lean_closure_set(v___f_1278_, 2, v___y_1272_);
v___x_1279_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1266_, v_maxFVars_x3f_1267_, v___f_1278_, v_cleanupAnnotations_1269_, v_whnfType_1270_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
if (lean_obj_tag(v___x_1279_) == 0)
{
return v___x_1279_;
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1279_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1279_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1288_, lean_object* v_maxFVars_x3f_1289_, lean_object* v_k_1290_, lean_object* v_cleanupAnnotations_1291_, lean_object* v_whnfType_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1300_; uint8_t v_whnfType_boxed_1301_; lean_object* v_res_1302_; 
v_cleanupAnnotations_boxed_1300_ = lean_unbox(v_cleanupAnnotations_1291_);
v_whnfType_boxed_1301_ = lean_unbox(v_whnfType_1292_);
v_res_1302_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1288_, v_maxFVars_x3f_1289_, v_k_1290_, v_cleanupAnnotations_boxed_1300_, v_whnfType_boxed_1301_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1303_, lean_object* v_type_1304_, lean_object* v_maxFVars_x3f_1305_, lean_object* v_k_1306_, uint8_t v_cleanupAnnotations_1307_, uint8_t v_whnfType_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1304_, v_maxFVars_x3f_1305_, v_k_1306_, v_cleanupAnnotations_1307_, v_whnfType_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_type_1318_, lean_object* v_maxFVars_x3f_1319_, lean_object* v_k_1320_, lean_object* v_cleanupAnnotations_1321_, lean_object* v_whnfType_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1330_; uint8_t v_whnfType_boxed_1331_; lean_object* v_res_1332_; 
v_cleanupAnnotations_boxed_1330_ = lean_unbox(v_cleanupAnnotations_1321_);
v_whnfType_boxed_1331_ = lean_unbox(v_whnfType_1322_);
v_res_1332_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1317_, v_type_1318_, v_maxFVars_x3f_1319_, v_k_1320_, v_cleanupAnnotations_boxed_1330_, v_whnfType_boxed_1331_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v_options_1341_; uint8_t v_hasTrace_1342_; 
v_options_1341_ = lean_ctor_get(v___y_1338_, 2);
v_hasTrace_1342_ = lean_ctor_get_uint8(v_options_1341_, sizeof(void*)*1);
if (v_hasTrace_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec(v_cls_1333_);
v___x_1343_ = lean_box(v_hasTrace_1342_);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
else
{
lean_object* v_inheritedTraceOptions_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_inheritedTraceOptions_1345_ = lean_ctor_get(v___y_1338_, 13);
v___x_1346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1347_ = l_Lean_Name_append(v___x_1346_, v_cls_1333_);
v___x_1348_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1345_, v_options_1341_, v___x_1347_);
lean_dec(v___x_1347_);
v___x_1349_ = lean_box(v___x_1348_);
v___x_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object* v_cls_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_mvarId_1360_, lean_object* v_val_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; lean_object* v_mctx_1365_; lean_object* v_cache_1366_; lean_object* v_zetaDeltaFVarIds_1367_; lean_object* v_postponed_1368_; lean_object* v_diag_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1397_; 
v___x_1364_ = lean_st_ref_take(v___y_1362_);
v_mctx_1365_ = lean_ctor_get(v___x_1364_, 0);
v_cache_1366_ = lean_ctor_get(v___x_1364_, 1);
v_zetaDeltaFVarIds_1367_ = lean_ctor_get(v___x_1364_, 2);
v_postponed_1368_ = lean_ctor_get(v___x_1364_, 3);
v_diag_1369_ = lean_ctor_get(v___x_1364_, 4);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1371_ = v___x_1364_;
v_isShared_1372_ = v_isSharedCheck_1397_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_diag_1369_);
lean_inc(v_postponed_1368_);
lean_inc(v_zetaDeltaFVarIds_1367_);
lean_inc(v_cache_1366_);
lean_inc(v_mctx_1365_);
lean_dec(v___x_1364_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1397_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_depth_1373_; lean_object* v_levelAssignDepth_1374_; lean_object* v_lmvarCounter_1375_; lean_object* v_mvarCounter_1376_; lean_object* v_lDecls_1377_; lean_object* v_decls_1378_; lean_object* v_userNames_1379_; lean_object* v_lAssignment_1380_; lean_object* v_eAssignment_1381_; lean_object* v_dAssignment_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1396_; 
v_depth_1373_ = lean_ctor_get(v_mctx_1365_, 0);
v_levelAssignDepth_1374_ = lean_ctor_get(v_mctx_1365_, 1);
v_lmvarCounter_1375_ = lean_ctor_get(v_mctx_1365_, 2);
v_mvarCounter_1376_ = lean_ctor_get(v_mctx_1365_, 3);
v_lDecls_1377_ = lean_ctor_get(v_mctx_1365_, 4);
v_decls_1378_ = lean_ctor_get(v_mctx_1365_, 5);
v_userNames_1379_ = lean_ctor_get(v_mctx_1365_, 6);
v_lAssignment_1380_ = lean_ctor_get(v_mctx_1365_, 7);
v_eAssignment_1381_ = lean_ctor_get(v_mctx_1365_, 8);
v_dAssignment_1382_ = lean_ctor_get(v_mctx_1365_, 9);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_mctx_1365_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1384_ = v_mctx_1365_;
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_dAssignment_1382_);
lean_inc(v_eAssignment_1381_);
lean_inc(v_lAssignment_1380_);
lean_inc(v_userNames_1379_);
lean_inc(v_decls_1378_);
lean_inc(v_lDecls_1377_);
lean_inc(v_mvarCounter_1376_);
lean_inc(v_lmvarCounter_1375_);
lean_inc(v_levelAssignDepth_1374_);
lean_inc(v_depth_1373_);
lean_dec(v_mctx_1365_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1396_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1381_, v_mvarId_1360_, v_val_1361_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 8, v___x_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_depth_1373_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_levelAssignDepth_1374_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_lmvarCounter_1375_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_mvarCounter_1376_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_lDecls_1377_);
lean_ctor_set(v_reuseFailAlloc_1395_, 5, v_decls_1378_);
lean_ctor_set(v_reuseFailAlloc_1395_, 6, v_userNames_1379_);
lean_ctor_set(v_reuseFailAlloc_1395_, 7, v_lAssignment_1380_);
lean_ctor_set(v_reuseFailAlloc_1395_, 8, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1395_, 9, v_dAssignment_1382_);
v___x_1388_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 0, v___x_1388_);
v___x_1390_ = v___x_1371_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_cache_1366_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_zetaDeltaFVarIds_1367_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_postponed_1368_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_diag_1369_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1391_ = lean_st_ref_set(v___y_1362_, v___x_1390_);
v___x_1392_ = lean_box(0);
v___x_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
return v___x_1393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_mvarId_1398_, lean_object* v_val_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1398_, v_val_1399_, v___y_1400_);
lean_dec(v___y_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_cls_1403_, lean_object* v_msg_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v_ref_1410_; lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1456_; 
v_ref_1410_ = lean_ctor_get(v___y_1407_, 5);
v___x_1411_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1456_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1456_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v_traceState_1417_; lean_object* v_env_1418_; lean_object* v_nextMacroScope_1419_; lean_object* v_ngen_1420_; lean_object* v_auxDeclNGen_1421_; lean_object* v_cache_1422_; lean_object* v_messages_1423_; lean_object* v_infoState_1424_; lean_object* v_snapshotTasks_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1455_; 
v___x_1416_ = lean_st_ref_take(v___y_1408_);
v_traceState_1417_ = lean_ctor_get(v___x_1416_, 4);
v_env_1418_ = lean_ctor_get(v___x_1416_, 0);
v_nextMacroScope_1419_ = lean_ctor_get(v___x_1416_, 1);
v_ngen_1420_ = lean_ctor_get(v___x_1416_, 2);
v_auxDeclNGen_1421_ = lean_ctor_get(v___x_1416_, 3);
v_cache_1422_ = lean_ctor_get(v___x_1416_, 5);
v_messages_1423_ = lean_ctor_get(v___x_1416_, 6);
v_infoState_1424_ = lean_ctor_get(v___x_1416_, 7);
v_snapshotTasks_1425_ = lean_ctor_get(v___x_1416_, 8);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1416_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1427_ = v___x_1416_;
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snapshotTasks_1425_);
lean_inc(v_infoState_1424_);
lean_inc(v_messages_1423_);
lean_inc(v_cache_1422_);
lean_inc(v_traceState_1417_);
lean_inc(v_auxDeclNGen_1421_);
lean_inc(v_ngen_1420_);
lean_inc(v_nextMacroScope_1419_);
lean_inc(v_env_1418_);
lean_dec(v___x_1416_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1455_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
uint64_t v_tid_1429_; lean_object* v_traces_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1454_; 
v_tid_1429_ = lean_ctor_get_uint64(v_traceState_1417_, sizeof(void*)*1);
v_traces_1430_ = lean_ctor_get(v_traceState_1417_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_traceState_1417_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1432_ = v_traceState_1417_;
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_traces_1430_);
lean_dec(v_traceState_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1454_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; double v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_1436_ = 0;
v___x_1437_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_1438_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1438_, 0, v_cls_1403_);
lean_ctor_set(v___x_1438_, 1, v___x_1434_);
lean_ctor_set(v___x_1438_, 2, v___x_1437_);
lean_ctor_set_float(v___x_1438_, sizeof(void*)*3, v___x_1435_);
lean_ctor_set_float(v___x_1438_, sizeof(void*)*3 + 8, v___x_1435_);
lean_ctor_set_uint8(v___x_1438_, sizeof(void*)*3 + 16, v___x_1436_);
v___x_1439_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_1440_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1438_);
lean_ctor_set(v___x_1440_, 1, v_a_1412_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
lean_inc(v_ref_1410_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_ref_1410_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_PersistentArray_push___redArg(v_traces_1430_, v___x_1441_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1442_);
v___x_1444_ = v___x_1432_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1442_);
lean_ctor_set_uint64(v_reuseFailAlloc_1453_, sizeof(void*)*1, v_tid_1429_);
v___x_1444_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1446_; 
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 4, v___x_1444_);
v___x_1446_ = v___x_1427_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_env_1418_);
lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_nextMacroScope_1419_);
lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_ngen_1420_);
lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_auxDeclNGen_1421_);
lean_ctor_set(v_reuseFailAlloc_1452_, 4, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1452_, 5, v_cache_1422_);
lean_ctor_set(v_reuseFailAlloc_1452_, 6, v_messages_1423_);
lean_ctor_set(v_reuseFailAlloc_1452_, 7, v_infoState_1424_);
lean_ctor_set(v_reuseFailAlloc_1452_, 8, v_snapshotTasks_1425_);
v___x_1446_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1447_ = lean_st_ref_set(v___y_1408_, v___x_1446_);
v___x_1448_ = lean_box(0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1448_);
v___x_1450_ = v___x_1414_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_cls_1457_, lean_object* v_msg_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1457_, v_msg_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
return v_res_1464_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1465_; lean_object* v_dummy_1466_; 
v___x_1465_ = lean_box(0);
v_dummy_1466_ = l_Lean_Expr_sort___override(v___x_1465_);
return v_dummy_1466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1));
v___x_1469_ = l_Lean_stringToMessageData(v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1471_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3));
v___x_1472_ = l_Lean_stringToMessageData(v___x_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v_numParams_1473_, lean_object* v___x_1474_, lean_object* v_name_1475_, lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v_name_1478_, lean_object* v___x_1479_, lean_object* v_cls_1480_, lean_object* v_fields_1481_, lean_object* v_bodyExpr_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
lean_object* v_options_1490_; lean_object* v_inheritedTraceOptions_1491_; uint8_t v_hasTrace_1492_; lean_object* v_nargs_1493_; lean_object* v_dummy_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; 
v_options_1490_ = lean_ctor_get(v___y_1487_, 2);
v_inheritedTraceOptions_1491_ = lean_ctor_get(v___y_1487_, 13);
v_hasTrace_1492_ = lean_ctor_get_uint8(v_options_1490_, sizeof(void*)*1);
v_nargs_1493_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1482_);
v_dummy_1494_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
lean_inc(v_nargs_1493_);
v___x_1495_ = lean_mk_array(v_nargs_1493_, v_dummy_1494_);
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_sub(v_nargs_1493_, v___x_1496_);
lean_dec(v_nargs_1493_);
v___x_1498_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1482_, v___x_1495_, v___x_1497_);
v___x_1499_ = lean_array_get_size(v___x_1498_);
v___x_1500_ = lean_nat_add(v_numParams_1473_, v___x_1474_);
v___x_1501_ = l_Array_toSubarray___redArg(v___x_1498_, v___x_1500_, v___x_1499_);
v___x_1502_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1475_);
lean_inc(v___x_1476_);
lean_inc(v___x_1502_);
v___x_1503_ = l_Lean_mkConst(v___x_1502_, v___x_1476_);
v___x_1504_ = l_Lean_mkAppN(v___x_1503_, v___x_1477_);
v___x_1505_ = l_Subarray_copy___redArg(v___x_1501_);
v___x_1506_ = l_Lean_mkAppN(v___x_1504_, v___x_1505_);
lean_dec_ref(v___x_1505_);
if (v_hasTrace_1492_ == 0)
{
lean_dec(v_cls_1480_);
v___y_1508_ = v___y_1483_;
v___y_1509_ = v___y_1484_;
v___y_1510_ = v___y_1485_;
v___y_1511_ = v___y_1486_;
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
lean_inc(v_cls_1480_);
v___x_1563_ = l_Lean_Name_append(v___x_1562_, v_cls_1480_);
v___x_1564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1491_, v_options_1490_, v___x_1563_);
lean_dec(v___x_1563_);
if (v___x_1564_ == 0)
{
lean_dec(v_cls_1480_);
v___y_1508_ = v___y_1483_;
v___y_1509_ = v___y_1484_;
v___y_1510_ = v___y_1485_;
v___y_1511_ = v___y_1486_;
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1565_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
lean_inc(v_name_1478_);
v___x_1566_ = l_Lean_MessageData_ofName(v_name_1478_);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
lean_inc_ref(v___x_1506_);
v___x_1570_ = l_Lean_MessageData_ofExpr(v___x_1506_);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1480_, v___x_1571_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_dec_ref_known(v___x_1572_, 1);
v___y_1508_ = v___y_1483_;
v___y_1509_ = v___y_1484_;
v___y_1510_ = v___y_1485_;
v___y_1511_ = v___y_1486_;
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
goto v___jp_1507_;
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___x_1506_);
lean_dec(v___x_1502_);
lean_dec(v_name_1478_);
lean_dec(v___x_1476_);
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
v___jp_1507_:
{
lean_object* v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1506_);
v___x_1515_ = 0;
v___x_1516_ = lean_box(0);
v___x_1517_ = l_Lean_Meta_mkFreshExprMVar(v___x_1514_, v___x_1515_, v___x_1516_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v_a_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v___x_1517_, 1);
v___x_1519_ = l_Lean_Expr_mvarId_x21(v_a_1518_);
lean_inc(v___x_1519_);
v___x_1520_ = l_Lean_MVarId_getType(v___x_1519_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v___x_1520_, 1);
v___x_1522_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1523_ = l_Lean_Name_append(v___x_1502_, v___x_1522_);
lean_inc(v___x_1476_);
v___x_1524_ = l_Lean_mkConst(v___x_1523_, v___x_1476_);
v___x_1525_ = l_Lean_mkAppN(v___x_1524_, v___x_1477_);
v___x_1526_ = 0;
v___x_1527_ = 1;
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1519_);
v___x_1529_ = l_Lean_MVarId_rewrite(v___x_1519_, v_a_1521_, v___x_1525_, v___x_1526_, v___x_1528_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v_eNew_1531_; lean_object* v_eqProof_1532_; lean_object* v___x_1533_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
v_eNew_1531_ = lean_ctor_get(v_a_1530_, 0);
lean_inc_ref(v_eNew_1531_);
v_eqProof_1532_ = lean_ctor_get(v_a_1530_, 1);
lean_inc_ref(v_eqProof_1532_);
lean_dec(v_a_1530_);
v___x_1533_ = l_Lean_MVarId_replaceTargetEq(v___x_1519_, v_eNew_1531_, v_eqProof_1532_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v_a_1541_; uint8_t v___x_1542_; lean_object* v___x_1543_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = l_Lean_mkConst(v_name_1478_, v___x_1476_);
v___x_1536_ = l_Lean_mkAppN(v___x_1535_, v___x_1477_);
v___x_1537_ = l_Lean_mkAppN(v___x_1536_, v___x_1479_);
v___x_1538_ = l_Lean_mkAppN(v___x_1537_, v_fields_1481_);
v___x_1539_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_1534_, v___x_1538_, v___y_1511_);
lean_dec_ref(v___x_1539_);
v___x_1540_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1518_, v___y_1511_);
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
v___x_1542_ = 1;
v___x_1543_ = l_Lean_Meta_mkLambdaFVars(v_fields_1481_, v_a_1541_, v___x_1526_, v___x_1527_, v___x_1526_, v___x_1527_, v___x_1542_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1545_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v___x_1543_, 1);
v___x_1545_ = l_Lean_Meta_mkLambdaFVars(v___x_1477_, v_a_1544_, v___x_1526_, v___x_1527_, v___x_1526_, v___x_1527_, v___x_1542_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1545_;
}
else
{
return v___x_1543_;
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v_a_1518_);
lean_dec(v_name_1478_);
lean_dec(v___x_1476_);
v_a_1546_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1533_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1533_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_dec(v___x_1519_);
lean_dec(v_a_1518_);
lean_dec(v_name_1478_);
lean_dec(v___x_1476_);
v_a_1554_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1529_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1529_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_dec(v___x_1519_);
lean_dec(v_a_1518_);
lean_dec(v___x_1502_);
lean_dec(v_name_1478_);
lean_dec(v___x_1476_);
return v___x_1520_;
}
}
else
{
lean_dec(v___x_1502_);
lean_dec(v_name_1478_);
lean_dec(v___x_1476_);
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_1581_ = _args[0];
lean_object* v___x_1582_ = _args[1];
lean_object* v_name_1583_ = _args[2];
lean_object* v___x_1584_ = _args[3];
lean_object* v___x_1585_ = _args[4];
lean_object* v_name_1586_ = _args[5];
lean_object* v___x_1587_ = _args[6];
lean_object* v_cls_1588_ = _args[7];
lean_object* v_fields_1589_ = _args[8];
lean_object* v_bodyExpr_1590_ = _args[9];
lean_object* v___y_1591_ = _args[10];
lean_object* v___y_1592_ = _args[11];
lean_object* v___y_1593_ = _args[12];
lean_object* v___y_1594_ = _args[13];
lean_object* v___y_1595_ = _args[14];
lean_object* v___y_1596_ = _args[15];
lean_object* v___y_1597_ = _args[16];
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1581_, v___x_1582_, v_name_1583_, v___x_1584_, v___x_1585_, v_name_1586_, v___x_1587_, v_cls_1588_, v_fields_1589_, v_bodyExpr_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v_fields_1589_);
lean_dec_ref(v___x_1587_);
lean_dec_ref(v___x_1585_);
lean_dec(v___x_1582_);
lean_dec(v_numParams_1581_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1599_, size_t v_sz_1600_, size_t v_i_1601_, lean_object* v_bs_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_usize_dec_lt(v_i_1601_, v_sz_1600_);
if (v___x_1603_ == 0)
{
return v_bs_1602_;
}
else
{
lean_object* v_v_1604_; lean_object* v___x_1605_; lean_object* v_bs_x27_1606_; lean_object* v___x_1607_; size_t v___x_1608_; size_t v___x_1609_; lean_object* v___x_1610_; 
v_v_1604_ = lean_array_uget(v_bs_1602_, v_i_1601_);
v___x_1605_ = lean_unsigned_to_nat(0u);
v_bs_x27_1606_ = lean_array_uset(v_bs_1602_, v_i_1601_, v___x_1605_);
v___x_1607_ = l_Lean_mkAppN(v_v_1604_, v___x_1599_);
v___x_1608_ = ((size_t)1ULL);
v___x_1609_ = lean_usize_add(v_i_1601_, v___x_1608_);
v___x_1610_ = lean_array_uset(v_bs_x27_1606_, v_i_1601_, v___x_1607_);
v_i_1601_ = v___x_1609_;
v_bs_1602_ = v___x_1610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1612_, lean_object* v_sz_1613_, lean_object* v_i_1614_, lean_object* v_bs_1615_){
_start:
{
size_t v_sz_boxed_1616_; size_t v_i_boxed_1617_; lean_object* v_res_1618_; 
v_sz_boxed_1616_ = lean_unbox_usize(v_sz_1613_);
lean_dec(v_sz_1613_);
v_i_boxed_1617_ = lean_unbox_usize(v_i_1614_);
lean_dec(v_i_1614_);
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1612_, v_sz_boxed_1616_, v_i_boxed_1617_, v_bs_1615_);
lean_dec_ref(v___x_1612_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1619_, size_t v_sz_1620_, size_t v_i_1621_, lean_object* v_bs_1622_){
_start:
{
uint8_t v___x_1623_; 
v___x_1623_ = lean_usize_dec_lt(v_i_1621_, v_sz_1620_);
if (v___x_1623_ == 0)
{
lean_dec(v___x_1619_);
return v_bs_1622_;
}
else
{
lean_object* v_v_1624_; lean_object* v___x_1625_; lean_object* v_bs_x27_1626_; lean_object* v___x_1627_; size_t v___x_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v_v_1624_ = lean_array_uget(v_bs_1622_, v_i_1621_);
v___x_1625_ = lean_unsigned_to_nat(0u);
v_bs_x27_1626_ = lean_array_uset(v_bs_1622_, v_i_1621_, v___x_1625_);
lean_inc(v___x_1619_);
v___x_1627_ = l_Lean_mkConst(v_v_1624_, v___x_1619_);
v___x_1628_ = ((size_t)1ULL);
v___x_1629_ = lean_usize_add(v_i_1621_, v___x_1628_);
v___x_1630_ = lean_array_uset(v_bs_x27_1626_, v_i_1621_, v___x_1627_);
v_i_1621_ = v___x_1629_;
v_bs_1622_ = v___x_1630_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1632_, lean_object* v_sz_1633_, lean_object* v_i_1634_, lean_object* v_bs_1635_){
_start:
{
size_t v_sz_boxed_1636_; size_t v_i_boxed_1637_; lean_object* v_res_1638_; 
v_sz_boxed_1636_ = lean_unbox_usize(v_sz_1633_);
lean_dec(v_sz_1633_);
v_i_boxed_1637_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1632_, v_sz_boxed_1636_, v_i_boxed_1637_, v_bs_1635_);
return v_res_1638_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object* v___x_1642_, lean_object* v_numParams_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, size_t v___x_1646_, lean_object* v___x_1647_, lean_object* v_name_1648_, lean_object* v_name_1649_, lean_object* v_cls_1650_, lean_object* v___f_1651_, lean_object* v_levelParams_1652_, lean_object* v_ctorSyntax_1653_, lean_object* v_args_1654_, lean_object* v_body_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; size_t v_sz_1666_; lean_object* v___x_1667_; size_t v_sz_1668_; lean_object* v___x_1669_; lean_object* v___f_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; lean_object* v___x_1674_; 
lean_inc_n(v_numParams_1643_, 2);
v___x_1663_ = l_Array_extract___redArg(v_args_1654_, v___x_1642_, v_numParams_1643_);
v___x_1664_ = lean_array_get_size(v_args_1654_);
v___x_1665_ = l_Array_toSubarray___redArg(v_args_1654_, v_numParams_1643_, v___x_1664_);
v_sz_1666_ = lean_array_size(v___x_1644_);
lean_inc(v___x_1645_);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1645_, v_sz_1666_, v___x_1646_, v___x_1644_);
v_sz_1668_ = lean_array_size(v___x_1667_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1663_, v_sz_1668_, v___x_1646_, v___x_1667_);
lean_inc(v_cls_1650_);
lean_inc_ref(v___x_1669_);
lean_inc(v_name_1649_);
v___f_1670_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1670_, 0, v_numParams_1643_);
lean_closure_set(v___f_1670_, 1, v___x_1647_);
lean_closure_set(v___f_1670_, 2, v_name_1648_);
lean_closure_set(v___f_1670_, 3, v___x_1645_);
lean_closure_set(v___f_1670_, 4, v___x_1663_);
lean_closure_set(v___f_1670_, 5, v_name_1649_);
lean_closure_set(v___f_1670_, 6, v___x_1669_);
lean_closure_set(v___f_1670_, 7, v_cls_1650_);
v___x_1671_ = l_Subarray_copy___redArg(v___x_1665_);
v___x_1672_ = l_Lean_Expr_replaceFVars(v_body_1655_, v___x_1671_, v___x_1669_);
lean_dec_ref(v___x_1669_);
lean_dec_ref(v___x_1671_);
v___x_1673_ = 0;
v___x_1674_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_1672_, v___f_1670_, v___x_1673_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v___x_1676_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
lean_inc_n(v_a_1675_, 2);
lean_dec_ref_known(v___x_1674_, 1);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
v___x_1676_ = lean_infer_type(v_a_1675_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___y_1679_; lean_object* v___y_1680_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___x_1701_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
v___x_1701_ = lean_apply_7(v___f_1651_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; uint8_t v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_unbox(v_a_1702_);
lean_dec(v_a_1702_);
if (v___x_1703_ == 0)
{
lean_dec(v_cls_1650_);
v___y_1679_ = v___y_1656_;
v___y_1680_ = v___y_1657_;
v___y_1681_ = v___y_1658_;
v___y_1682_ = v___y_1659_;
v___y_1683_ = v___y_1660_;
v___y_1684_ = v___y_1661_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1704_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
lean_inc(v_a_1677_);
v___x_1705_ = l_Lean_MessageData_ofExpr(v_a_1677_);
v___x_1706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1704_);
lean_ctor_set(v___x_1706_, 1, v___x_1705_);
v___x_1707_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1650_, v___x_1706_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_dec_ref_known(v___x_1707_, 1);
v___y_1679_ = v___y_1656_;
v___y_1680_ = v___y_1657_;
v___y_1681_ = v___y_1658_;
v___y_1682_ = v___y_1659_;
v___y_1683_ = v___y_1660_;
v___y_1684_ = v___y_1661_;
goto v___jp_1678_;
}
else
{
lean_dec(v_a_1677_);
lean_dec(v_a_1675_);
lean_dec(v_ctorSyntax_1653_);
lean_dec(v_levelParams_1652_);
lean_dec(v_name_1649_);
return v___x_1707_;
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_a_1677_);
lean_dec(v_a_1675_);
lean_dec(v_ctorSyntax_1653_);
lean_dec(v_levelParams_1652_);
lean_dec(v_cls_1650_);
lean_dec(v_name_1649_);
v_a_1708_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1701_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1701_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
v___jp_1678_:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1700_; 
v___x_1685_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1649_);
v___x_1686_ = lean_box(0);
lean_inc(v_a_1675_);
v___x_1687_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1685_, v_levelParams_1652_, v_a_1677_, v_a_1675_, v___x_1686_, v___y_1684_);
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1700_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1700_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
lean_ctor_set_tag(v___x_1690_, 1);
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_addDecl(v___x_1693_, v___x_1673_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___x_1698_; 
lean_dec_ref_known(v___x_1694_, 1);
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_box(0);
v___x_1697_ = 1;
v___x_1698_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1653_, v_a_1675_, v___x_1695_, v___x_1695_, v___x_1696_, v___x_1697_, v___x_1673_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1698_;
}
else
{
lean_dec(v_a_1675_);
lean_dec(v_ctorSyntax_1653_);
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_a_1675_);
lean_dec(v_ctorSyntax_1653_);
lean_dec(v_levelParams_1652_);
lean_dec_ref(v___f_1651_);
lean_dec(v_cls_1650_);
lean_dec(v_name_1649_);
v_a_1716_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1676_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1676_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec(v_ctorSyntax_1653_);
lean_dec(v_levelParams_1652_);
lean_dec_ref(v___f_1651_);
lean_dec(v_cls_1650_);
lean_dec(v_name_1649_);
v_a_1724_ = lean_ctor_get(v___x_1674_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1674_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1674_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object** _args){
lean_object* v___x_1732_ = _args[0];
lean_object* v_numParams_1733_ = _args[1];
lean_object* v___x_1734_ = _args[2];
lean_object* v___x_1735_ = _args[3];
lean_object* v___x_1736_ = _args[4];
lean_object* v___x_1737_ = _args[5];
lean_object* v_name_1738_ = _args[6];
lean_object* v_name_1739_ = _args[7];
lean_object* v_cls_1740_ = _args[8];
lean_object* v___f_1741_ = _args[9];
lean_object* v_levelParams_1742_ = _args[10];
lean_object* v_ctorSyntax_1743_ = _args[11];
lean_object* v_args_1744_ = _args[12];
lean_object* v_body_1745_ = _args[13];
lean_object* v___y_1746_ = _args[14];
lean_object* v___y_1747_ = _args[15];
lean_object* v___y_1748_ = _args[16];
lean_object* v___y_1749_ = _args[17];
lean_object* v___y_1750_ = _args[18];
lean_object* v___y_1751_ = _args[19];
lean_object* v___y_1752_ = _args[20];
_start:
{
size_t v___x_9125__boxed_1753_; lean_object* v_res_1754_; 
v___x_9125__boxed_1753_ = lean_unbox_usize(v___x_1736_);
lean_dec(v___x_1736_);
v_res_1754_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1732_, v_numParams_1733_, v___x_1734_, v___x_1735_, v___x_9125__boxed_1753_, v___x_1737_, v_name_1738_, v_name_1739_, v_cls_1740_, v___f_1741_, v_levelParams_1742_, v_ctorSyntax_1743_, v_args_1744_, v_body_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec_ref(v_body_1745_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1755_, size_t v_i_1756_, lean_object* v_bs_1757_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_lt(v_i_1756_, v_sz_1755_);
if (v___x_1758_ == 0)
{
return v_bs_1757_;
}
else
{
lean_object* v_v_1759_; lean_object* v_toConstantVal_1760_; lean_object* v_name_1761_; lean_object* v___x_1762_; lean_object* v_bs_x27_1763_; lean_object* v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
v_v_1759_ = lean_array_uget_borrowed(v_bs_1757_, v_i_1756_);
v_toConstantVal_1760_ = lean_ctor_get(v_v_1759_, 0);
v_name_1761_ = lean_ctor_get(v_toConstantVal_1760_, 0);
lean_inc(v_name_1761_);
v___x_1762_ = lean_unsigned_to_nat(0u);
v_bs_x27_1763_ = lean_array_uset(v_bs_1757_, v_i_1756_, v___x_1762_);
v___x_1764_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1761_);
v___x_1765_ = ((size_t)1ULL);
v___x_1766_ = lean_usize_add(v_i_1756_, v___x_1765_);
v___x_1767_ = lean_array_uset(v_bs_x27_1763_, v_i_1756_, v___x_1764_);
v_i_1756_ = v___x_1766_;
v_bs_1757_ = v___x_1767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1769_, lean_object* v_i_1770_, lean_object* v_bs_1771_){
_start:
{
size_t v_sz_boxed_1772_; size_t v_i_boxed_1773_; lean_object* v_res_1774_; 
v_sz_boxed_1772_ = lean_unbox_usize(v_sz_1769_);
lean_dec(v_sz_1769_);
v_i_boxed_1773_ = lean_unbox_usize(v_i_1770_);
lean_dec(v_i_1770_);
v_res_1774_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1772_, v_i_boxed_1773_, v_bs_1771_);
return v_res_1774_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1));
v___x_1779_ = l_Lean_stringToMessageData(v___x_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1782_, lean_object* v_ctorSyntax_1783_, lean_object* v_numParams_1784_, lean_object* v_name_1785_, lean_object* v_ctor_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_cls_1794_; lean_object* v___f_1795_; lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1839_; 
v_cls_1794_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___f_1795_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1796_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1794_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1799_ = v___x_1796_;
v_isShared_1800_ = v_isSharedCheck_1839_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1796_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1839_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; uint8_t v___x_1831_; 
v___x_1801_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1831_ = lean_unbox(v_a_1797_);
lean_dec(v_a_1797_);
if (v___x_1831_ == 0)
{
v___y_1803_ = v_a_1787_;
v___y_1804_ = v_a_1788_;
v___y_1805_ = v_a_1789_;
v___y_1806_ = v_a_1790_;
v___y_1807_ = v_a_1791_;
v___y_1808_ = v_a_1792_;
goto v___jp_1802_;
}
else
{
lean_object* v_toConstantVal_1832_; lean_object* v_name_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v_toConstantVal_1832_ = lean_ctor_get(v_ctor_1786_, 0);
v_name_1833_ = lean_ctor_get(v_toConstantVal_1832_, 0);
v___x_1834_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
lean_inc(v_name_1833_);
v___x_1835_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1833_);
v___x_1836_ = l_Lean_MessageData_ofName(v___x_1835_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1834_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1794_, v___x_1837_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_dec_ref_known(v___x_1838_, 1);
v___y_1803_ = v_a_1787_;
v___y_1804_ = v_a_1788_;
v___y_1805_ = v_a_1789_;
v___y_1806_ = v_a_1790_;
v___y_1807_ = v_a_1791_;
v___y_1808_ = v_a_1792_;
goto v___jp_1802_;
}
else
{
lean_del_object(v___x_1799_);
lean_dec_ref(v_ctor_1786_);
lean_dec(v_name_1785_);
lean_dec(v_numParams_1784_);
lean_dec(v_ctorSyntax_1783_);
lean_dec_ref(v_infos_1782_);
return v___x_1838_;
}
}
v___jp_1802_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v_toConstantVal_1811_; lean_object* v_toConstantVal_1812_; lean_object* v_levelParams_1813_; lean_object* v_name_1814_; lean_object* v_levelParams_1815_; lean_object* v_type_1816_; lean_object* v___x_1817_; size_t v_sz_1818_; size_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_array_get_borrowed(v___x_1801_, v_infos_1782_, v___x_1809_);
v_toConstantVal_1811_ = lean_ctor_get(v___x_1810_, 0);
v_toConstantVal_1812_ = lean_ctor_get(v_ctor_1786_, 0);
lean_inc_ref(v_toConstantVal_1812_);
lean_dec_ref(v_ctor_1786_);
v_levelParams_1813_ = lean_ctor_get(v_toConstantVal_1811_, 1);
lean_inc(v_levelParams_1813_);
v_name_1814_ = lean_ctor_get(v_toConstantVal_1812_, 0);
lean_inc(v_name_1814_);
v_levelParams_1815_ = lean_ctor_get(v_toConstantVal_1812_, 1);
lean_inc(v_levelParams_1815_);
v_type_1816_ = lean_ctor_get(v_toConstantVal_1812_, 2);
lean_inc_ref(v_type_1816_);
lean_dec_ref(v_toConstantVal_1812_);
v___x_1817_ = lean_array_get_size(v_infos_1782_);
v_sz_1818_ = lean_array_size(v_infos_1782_);
v___x_1819_ = ((size_t)0ULL);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1818_, v___x_1819_, v_infos_1782_);
v___x_1821_ = lean_box(0);
v___x_1822_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1813_, v___x_1821_);
v___x_1823_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1784_);
v___f_1824_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed), 21, 12);
lean_closure_set(v___f_1824_, 0, v___x_1809_);
lean_closure_set(v___f_1824_, 1, v_numParams_1784_);
lean_closure_set(v___f_1824_, 2, v___x_1820_);
lean_closure_set(v___f_1824_, 3, v___x_1822_);
lean_closure_set(v___f_1824_, 4, v___x_1823_);
lean_closure_set(v___f_1824_, 5, v___x_1817_);
lean_closure_set(v___f_1824_, 6, v_name_1785_);
lean_closure_set(v___f_1824_, 7, v_name_1814_);
lean_closure_set(v___f_1824_, 8, v_cls_1794_);
lean_closure_set(v___f_1824_, 9, v___f_1795_);
lean_closure_set(v___f_1824_, 10, v_levelParams_1815_);
lean_closure_set(v___f_1824_, 11, v_ctorSyntax_1783_);
v___x_1825_ = lean_nat_add(v_numParams_1784_, v___x_1817_);
lean_dec(v_numParams_1784_);
if (v_isShared_1800_ == 0)
{
lean_ctor_set_tag(v___x_1799_, 1);
lean_ctor_set(v___x_1799_, 0, v___x_1825_);
v___x_1827_ = v___x_1799_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
uint8_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1828_ = 0;
v___x_1829_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1816_, v___x_1827_, v___f_1824_, v___x_1828_, v___x_1828_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1840_, lean_object* v_ctorSyntax_1841_, lean_object* v_numParams_1842_, lean_object* v_name_1843_, lean_object* v_ctor_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1840_, v_ctorSyntax_1841_, v_numParams_1842_, v_name_1843_, v_ctor_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec_ref(v_a_1845_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_mvarId_1853_, lean_object* v_val_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1853_, v_val_1854_, v___y_1858_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_mvarId_1863_, lean_object* v_val_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1863_, v_val_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_cls_1873_, lean_object* v_msg_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1873_, v_msg_1874_, v___y_1877_, v___y_1878_, v___y_1879_, v___y_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_cls_1883_, lean_object* v_msg_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1883_, v_msg_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1892_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_instMonadEIO(lean_box(0));
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_toApplicative_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_2001_; 
v___x_1908_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1909_ = l_StateRefT_x27_instMonad___redArg(v___x_1908_);
v_toApplicative_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v___x_1909_, 1);
lean_dec(v_unused_2002_);
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_2001_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_toApplicative_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_2001_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v_toFunctor_1914_; lean_object* v_toSeq_1915_; lean_object* v_toSeqLeft_1916_; lean_object* v_toSeqRight_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1999_; 
v_toFunctor_1914_ = lean_ctor_get(v_toApplicative_1910_, 0);
v_toSeq_1915_ = lean_ctor_get(v_toApplicative_1910_, 2);
v_toSeqLeft_1916_ = lean_ctor_get(v_toApplicative_1910_, 3);
v_toSeqRight_1917_ = lean_ctor_get(v_toApplicative_1910_, 4);
v_isSharedCheck_1999_ = !lean_is_exclusive(v_toApplicative_1910_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; 
v_unused_2000_ = lean_ctor_get(v_toApplicative_1910_, 1);
lean_dec(v_unused_2000_);
v___x_1919_ = v_toApplicative_1910_;
v_isShared_1920_ = v_isSharedCheck_1999_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_toSeqRight_1917_);
lean_inc(v_toSeqLeft_1916_);
lean_inc(v_toSeq_1915_);
lean_inc(v_toFunctor_1914_);
lean_dec(v_toApplicative_1910_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1999_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___f_1921_; lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; lean_object* v___f_1926_; lean_object* v___f_1927_; lean_object* v___f_1928_; lean_object* v___x_1930_; 
v___f_1921_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1922_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1914_);
v___f_1923_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1923_, 0, v_toFunctor_1914_);
v___f_1924_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1924_, 0, v_toFunctor_1914_);
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___f_1923_);
lean_ctor_set(v___x_1925_, 1, v___f_1924_);
v___f_1926_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1926_, 0, v_toSeqRight_1917_);
v___f_1927_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1927_, 0, v_toSeqLeft_1916_);
v___f_1928_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1928_, 0, v_toSeq_1915_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 4, v___f_1926_);
lean_ctor_set(v___x_1919_, 3, v___f_1927_);
lean_ctor_set(v___x_1919_, 2, v___f_1928_);
lean_ctor_set(v___x_1919_, 1, v___f_1921_);
lean_ctor_set(v___x_1919_, 0, v___x_1925_);
v___x_1930_ = v___x_1919_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v___f_1921_);
lean_ctor_set(v_reuseFailAlloc_1998_, 2, v___f_1928_);
lean_ctor_set(v_reuseFailAlloc_1998_, 3, v___f_1927_);
lean_ctor_set(v_reuseFailAlloc_1998_, 4, v___f_1926_);
v___x_1930_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1932_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v___f_1922_);
lean_ctor_set(v___x_1912_, 0, v___x_1930_);
v___x_1932_ = v___x_1912_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___f_1922_);
v___x_1932_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v_toApplicative_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1995_; 
v___x_1933_ = l_StateRefT_x27_instMonad___redArg(v___x_1932_);
v_toApplicative_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1933_, 1);
lean_dec(v_unused_1996_);
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1995_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_toApplicative_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1995_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v_toFunctor_1938_; lean_object* v_toSeq_1939_; lean_object* v_toSeqLeft_1940_; lean_object* v_toSeqRight_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1993_; 
v_toFunctor_1938_ = lean_ctor_get(v_toApplicative_1934_, 0);
v_toSeq_1939_ = lean_ctor_get(v_toApplicative_1934_, 2);
v_toSeqLeft_1940_ = lean_ctor_get(v_toApplicative_1934_, 3);
v_toSeqRight_1941_ = lean_ctor_get(v_toApplicative_1934_, 4);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_toApplicative_1934_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v_toApplicative_1934_, 1);
lean_dec(v_unused_1994_);
v___x_1943_ = v_toApplicative_1934_;
v_isShared_1944_ = v_isSharedCheck_1993_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_toSeqRight_1941_);
lean_inc(v_toSeqLeft_1940_);
lean_inc(v_toSeq_1939_);
lean_inc(v_toFunctor_1938_);
lean_dec(v_toApplicative_1934_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1993_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___f_1945_; lean_object* v___f_1946_; lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___x_1954_; 
v___f_1945_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1946_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1938_);
v___f_1947_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1947_, 0, v_toFunctor_1938_);
v___f_1948_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1948_, 0, v_toFunctor_1938_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___f_1947_);
lean_ctor_set(v___x_1949_, 1, v___f_1948_);
v___f_1950_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1950_, 0, v_toSeqRight_1941_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toSeqLeft_1940_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toSeq_1939_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 4, v___f_1950_);
lean_ctor_set(v___x_1943_, 3, v___f_1951_);
lean_ctor_set(v___x_1943_, 2, v___f_1952_);
lean_ctor_set(v___x_1943_, 1, v___f_1945_);
lean_ctor_set(v___x_1943_, 0, v___x_1949_);
v___x_1954_ = v___x_1943_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___f_1945_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v___f_1952_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v___f_1951_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v___f_1950_);
v___x_1954_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1956_; 
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 1, v___f_1946_);
lean_ctor_set(v___x_1936_, 0, v___x_1954_);
v___x_1956_ = v___x_1936_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1954_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___f_1946_);
v___x_1956_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1957_; lean_object* v_toApplicative_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1989_; 
v___x_1957_ = l_StateRefT_x27_instMonad___redArg(v___x_1956_);
v_toApplicative_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; 
v_unused_1990_ = lean_ctor_get(v___x_1957_, 1);
lean_dec(v_unused_1990_);
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1989_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_toApplicative_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1989_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_toFunctor_1962_; lean_object* v_toSeq_1963_; lean_object* v_toSeqLeft_1964_; lean_object* v_toSeqRight_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1987_; 
v_toFunctor_1962_ = lean_ctor_get(v_toApplicative_1958_, 0);
v_toSeq_1963_ = lean_ctor_get(v_toApplicative_1958_, 2);
v_toSeqLeft_1964_ = lean_ctor_get(v_toApplicative_1958_, 3);
v_toSeqRight_1965_ = lean_ctor_get(v_toApplicative_1958_, 4);
v_isSharedCheck_1987_ = !lean_is_exclusive(v_toApplicative_1958_);
if (v_isSharedCheck_1987_ == 0)
{
lean_object* v_unused_1988_; 
v_unused_1988_ = lean_ctor_get(v_toApplicative_1958_, 1);
lean_dec(v_unused_1988_);
v___x_1967_ = v_toApplicative_1958_;
v_isShared_1968_ = v_isSharedCheck_1987_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_toSeqRight_1965_);
lean_inc(v_toSeqLeft_1964_);
lean_inc(v_toSeq_1963_);
lean_inc(v_toFunctor_1962_);
lean_dec(v_toApplicative_1958_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1987_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___f_1969_; lean_object* v___f_1970_; lean_object* v___f_1971_; lean_object* v___f_1972_; lean_object* v___x_1973_; lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_1978_; 
v___f_1969_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_1970_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1962_);
v___f_1971_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1971_, 0, v_toFunctor_1962_);
v___f_1972_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1972_, 0, v_toFunctor_1962_);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___f_1971_);
lean_ctor_set(v___x_1973_, 1, v___f_1972_);
v___f_1974_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1974_, 0, v_toSeqRight_1965_);
v___f_1975_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1975_, 0, v_toSeqLeft_1964_);
v___f_1976_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1976_, 0, v_toSeq_1963_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 4, v___f_1974_);
lean_ctor_set(v___x_1967_, 3, v___f_1975_);
lean_ctor_set(v___x_1967_, 2, v___f_1976_);
lean_ctor_set(v___x_1967_, 1, v___f_1969_);
lean_ctor_set(v___x_1967_, 0, v___x_1973_);
v___x_1978_ = v___x_1967_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___f_1969_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v___f_1976_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v___f_1975_);
lean_ctor_set(v_reuseFailAlloc_1986_, 4, v___f_1974_);
v___x_1978_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v___x_1980_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v___f_1970_);
lean_ctor_set(v___x_1960_, 0, v___x_1978_);
v___x_1980_ = v___x_1960_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___f_1970_);
v___x_1980_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_3780__overap_1983_; lean_object* v___x_1984_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = l_instInhabitedOfMonad___redArg(v___x_1980_, v___x_1981_);
v___x_3780__overap_1983_ = lean_panic_fn_borrowed(v___x_1982_, v_msg_1900_);
lean_dec(v___x_1982_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
lean_inc(v___y_1902_);
lean_inc_ref(v___y_1901_);
v___x_1984_ = lean_apply_7(v___x_3780__overap_1983_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, lean_box(0));
return v___x_1984_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2011_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2012_, lean_object* v_opt_2013_){
_start:
{
lean_object* v_name_2014_; lean_object* v_defValue_2015_; lean_object* v_map_2016_; lean_object* v___x_2017_; 
v_name_2014_ = lean_ctor_get(v_opt_2013_, 0);
v_defValue_2015_ = lean_ctor_get(v_opt_2013_, 1);
v_map_2016_ = lean_ctor_get(v_opts_2012_, 0);
v___x_2017_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2016_, v_name_2014_);
if (lean_obj_tag(v___x_2017_) == 0)
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_unbox(v_defValue_2015_);
return v___x_2018_;
}
else
{
lean_object* v_val_2019_; 
v_val_2019_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_val_2019_);
lean_dec_ref_known(v___x_2017_, 1);
if (lean_obj_tag(v_val_2019_) == 1)
{
uint8_t v_v_2020_; 
v_v_2020_ = lean_ctor_get_uint8(v_val_2019_, 0);
lean_dec_ref_known(v_val_2019_, 0);
return v_v_2020_;
}
else
{
uint8_t v___x_2021_; 
lean_dec(v_val_2019_);
v___x_2021_ = lean_unbox(v_defValue_2015_);
return v___x_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2022_, lean_object* v_opt_2023_){
_start:
{
uint8_t v_res_2024_; lean_object* v_r_2025_; 
v_res_2024_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2022_, v_opt_2023_);
lean_dec_ref(v_opt_2023_);
lean_dec_ref(v_opts_2022_);
v_r_2025_ = lean_box(v_res_2024_);
return v_r_2025_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = lean_box(1);
v___x_2027_ = l_Lean_MessageData_ofFormat(v___x_2026_);
return v___x_2027_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2032_ = l_Lean_MessageData_ofFormat(v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2033_, lean_object* v_x_2034_){
_start:
{
if (lean_obj_tag(v_x_2034_) == 0)
{
return v_x_2033_;
}
else
{
lean_object* v_head_2035_; lean_object* v_tail_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2058_; 
v_head_2035_ = lean_ctor_get(v_x_2034_, 0);
v_tail_2036_ = lean_ctor_get(v_x_2034_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_x_2034_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2038_ = v_x_2034_;
v_isShared_2039_ = v_isSharedCheck_2058_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_tail_2036_);
lean_inc(v_head_2035_);
lean_dec(v_x_2034_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2058_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_before_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2056_; 
v_before_2040_ = lean_ctor_get(v_head_2035_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_head_2035_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_head_2035_, 1);
lean_dec(v_unused_2057_);
v___x_2042_ = v_head_2035_;
v_isShared_2043_ = v_isSharedCheck_2056_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_before_2040_);
lean_dec(v_head_2035_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2056_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2044_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 7);
lean_ctor_set(v___x_2042_, 1, v___x_2044_);
lean_ctor_set(v___x_2042_, 0, v_x_2033_);
v___x_2046_ = v___x_2042_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_x_2033_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2039_ == 0)
{
lean_ctor_set_tag(v___x_2038_, 7);
lean_ctor_set(v___x_2038_, 1, v___x_2047_);
lean_ctor_set(v___x_2038_, 0, v___x_2046_);
v___x_2049_ = v___x_2038_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = l_Lean_MessageData_ofSyntax(v_before_2040_);
v___x_2051_ = l_Lean_indentD(v___x_2050_);
v___x_2052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2049_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v_x_2033_ = v___x_2052_;
v_x_2034_ = v_tail_2036_;
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
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2063_ = l_Lean_MessageData_ofFormat(v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2064_, lean_object* v_macroStack_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_options_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v_options_2068_ = lean_ctor_get(v___y_2066_, 2);
v___x_2069_ = l_Lean_Elab_pp_macroStack;
v___x_2070_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_options_2068_, v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; 
lean_dec(v_macroStack_2065_);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v_msgData_2064_);
return v___x_2071_;
}
else
{
if (lean_obj_tag(v_macroStack_2065_) == 0)
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_msgData_2064_);
return v___x_2072_;
}
else
{
lean_object* v_head_2073_; lean_object* v_after_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2089_; 
v_head_2073_ = lean_ctor_get(v_macroStack_2065_, 0);
lean_inc(v_head_2073_);
v_after_2074_ = lean_ctor_get(v_head_2073_, 1);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_head_2073_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v_head_2073_, 0);
lean_dec(v_unused_2090_);
v___x_2076_ = v_head_2073_;
v_isShared_2077_ = v_isSharedCheck_2089_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_after_2074_);
lean_dec(v_head_2073_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2089_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2077_ == 0)
{
lean_ctor_set_tag(v___x_2076_, 7);
lean_ctor_set(v___x_2076_, 1, v___x_2078_);
lean_ctor_set(v___x_2076_, 0, v_msgData_2064_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_msgData_2064_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v_msgData_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2081_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_MessageData_ofSyntax(v_after_2074_);
v___x_2084_ = l_Lean_indentD(v___x_2083_);
v_msgData_2085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2085_, 0, v___x_2082_);
lean_ctor_set(v_msgData_2085_, 1, v___x_2084_);
v___x_2086_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2085_, v_macroStack_2065_);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2091_, lean_object* v_macroStack_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2091_, v_macroStack_2092_, v___y_2093_);
lean_dec_ref(v___y_2093_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_ref_2104_; lean_object* v___x_2105_; lean_object* v_a_2106_; lean_object* v_macroStack_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_ref_2104_ = lean_ctor_get(v___y_2101_, 5);
v___x_2105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2096_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v_macroStack_2107_ = lean_ctor_get(v___y_2097_, 1);
v___x_2108_ = l_Lean_Elab_getBetterRef(v_ref_2104_, v_macroStack_2107_);
lean_inc(v_macroStack_2107_);
v___x_2109_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2106_, v_macroStack_2107_, v___y_2101_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2112_ = v___x_2109_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2108_);
lean_ctor_set(v___x_2114_, 1, v_a_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 1);
lean_ctor_set(v___x_2112_, 0, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2127_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2130_ = l_Lean_stringToMessageData(v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2137_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2138_ = lean_unsigned_to_nat(11u);
v___x_2139_ = lean_unsigned_to_nat(122u);
v___x_2140_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2141_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2142_ = l_mkPanicMessageWithDecl(v___x_2141_, v___x_2140_, v___x_2139_, v___x_2138_, v___x_2137_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2159_; lean_object* v_env_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2159_ = lean_st_ref_get(v___y_2149_);
v_env_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc_ref(v_env_2160_);
lean_dec(v___x_2159_);
v___x_2161_ = 0;
lean_inc(v_constName_2143_);
v___x_2162_ = l_Lean_Environment_findAsync_x3f(v_env_2160_, v_constName_2143_, v___x_2161_);
if (lean_obj_tag(v___x_2162_) == 1)
{
lean_object* v_val_2163_; uint8_t v_kind_2164_; 
v_val_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_val_2163_);
lean_dec_ref_known(v___x_2162_, 1);
v_kind_2164_ = lean_ctor_get_uint8(v_val_2163_, sizeof(void*)*3);
if (v_kind_2164_ == 6)
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2163_);
if (lean_obj_tag(v___x_2165_) == 6)
{
lean_object* v_val_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_constName_2143_);
v_val_2166_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2165_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_val_2166_);
lean_dec(v___x_2165_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set_tag(v___x_2168_, 0);
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_val_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v___x_2165_);
v___x_2174_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2175_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2174_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2184_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2184_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
if (lean_obj_tag(v_a_2176_) == 0)
{
lean_del_object(v___x_2178_);
goto v___jp_2151_;
}
else
{
lean_object* v_val_2180_; lean_object* v___x_2182_; 
lean_dec(v_constName_2143_);
v_val_2180_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_val_2180_);
lean_dec_ref_known(v_a_2176_, 1);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v_val_2180_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_val_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_constName_2143_);
v_a_2185_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2175_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2175_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
else
{
lean_dec(v_val_2163_);
goto v___jp_2151_;
}
}
else
{
lean_dec(v___x_2162_);
goto v___jp_2151_;
}
v___jp_2151_:
{
lean_object* v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2152_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2153_ = 0;
v___x_2154_ = l_Lean_MessageData_ofConstName(v_constName_2143_, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2152_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2157_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2202_, lean_object* v_infos_2203_, lean_object* v_numParams_2204_, lean_object* v_as_x27_2205_, lean_object* v_b_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
if (lean_obj_tag(v_as_x27_2205_) == 0)
{
lean_object* v___x_2214_; 
lean_dec(v_numParams_2204_);
lean_dec_ref(v_infos_2203_);
lean_dec_ref(v_a_2202_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_b_2206_);
return v___x_2214_;
}
else
{
lean_object* v_head_2215_; lean_object* v_tail_2216_; lean_object* v_array_2217_; lean_object* v_start_2218_; lean_object* v_stop_2219_; uint8_t v___x_2220_; 
v_head_2215_ = lean_ctor_get(v_as_x27_2205_, 0);
v_tail_2216_ = lean_ctor_get(v_as_x27_2205_, 1);
v_array_2217_ = lean_ctor_get(v_b_2206_, 0);
v_start_2218_ = lean_ctor_get(v_b_2206_, 1);
v_stop_2219_ = lean_ctor_get(v_b_2206_, 2);
v___x_2220_ = lean_nat_dec_lt(v_start_2218_, v_stop_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; 
lean_dec(v_numParams_2204_);
lean_dec_ref(v_infos_2203_);
lean_dec_ref(v_a_2202_);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_b_2206_);
return v___x_2221_;
}
else
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2253_; 
lean_inc(v_stop_2219_);
lean_inc(v_start_2218_);
lean_inc_ref(v_array_2217_);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_b_2206_);
if (v_isSharedCheck_2253_ == 0)
{
lean_object* v_unused_2254_; lean_object* v_unused_2255_; lean_object* v_unused_2256_; 
v_unused_2254_ = lean_ctor_get(v_b_2206_, 2);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_b_2206_, 1);
lean_dec(v_unused_2255_);
v_unused_2256_ = lean_ctor_get(v_b_2206_, 0);
lean_dec(v_unused_2256_);
v___x_2223_ = v_b_2206_;
v_isShared_2224_ = v_isSharedCheck_2253_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v_b_2206_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2253_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; 
lean_inc(v_head_2215_);
v___x_2225_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2215_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_toConstantVal_2226_; lean_object* v_a_2227_; lean_object* v_name_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v_toConstantVal_2226_ = lean_ctor_get(v_a_2202_, 0);
v_a_2227_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2225_, 1);
v_name_2228_ = lean_ctor_get(v_toConstantVal_2226_, 0);
v___x_2229_ = lean_array_fget_borrowed(v_array_2217_, v_start_2218_);
lean_inc(v_name_2228_);
lean_inc(v_numParams_2204_);
lean_inc(v___x_2229_);
lean_inc_ref(v_infos_2203_);
v___x_2230_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2203_, v___x_2229_, v_numParams_2204_, v_name_2228_, v_a_2227_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
lean_dec_ref_known(v___x_2230_, 1);
v___x_2231_ = lean_unsigned_to_nat(1u);
v___x_2232_ = lean_nat_add(v_start_2218_, v___x_2231_);
lean_dec(v_start_2218_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 1, v___x_2232_);
v___x_2234_ = v___x_2223_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_array_2217_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2232_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_stop_2219_);
v___x_2234_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v_as_x27_2205_ = v_tail_2216_;
v_b_2206_ = v___x_2234_;
goto _start;
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_del_object(v___x_2223_);
lean_dec(v_stop_2219_);
lean_dec(v_start_2218_);
lean_dec_ref(v_array_2217_);
lean_dec(v_numParams_2204_);
lean_dec_ref(v_infos_2203_);
lean_dec_ref(v_a_2202_);
v_a_2237_ = lean_ctor_get(v___x_2230_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2230_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2230_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2230_);
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
lean_del_object(v___x_2223_);
lean_dec(v_stop_2219_);
lean_dec(v_start_2218_);
lean_dec_ref(v_array_2217_);
lean_dec(v_numParams_2204_);
lean_dec_ref(v_infos_2203_);
lean_dec_ref(v_a_2202_);
v_a_2245_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2225_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2225_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2257_, lean_object* v_infos_2258_, lean_object* v_numParams_2259_, lean_object* v_as_x27_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2257_, v_infos_2258_, v_numParams_2259_, v_as_x27_2260_, v_b_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v_as_x27_2260_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2270_, lean_object* v_numParams_2271_, lean_object* v_as_2272_, size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_b_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_usize_dec_lt(v_i_2274_, v_sz_2273_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec(v_numParams_2271_);
lean_dec_ref(v_infos_2270_);
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v_b_2275_);
return v___x_2284_;
}
else
{
lean_object* v_array_2285_; lean_object* v_start_2286_; lean_object* v_stop_2287_; uint8_t v___x_2288_; 
v_array_2285_ = lean_ctor_get(v_b_2275_, 0);
v_start_2286_ = lean_ctor_get(v_b_2275_, 1);
v_stop_2287_ = lean_ctor_get(v_b_2275_, 2);
v___x_2288_ = lean_nat_dec_lt(v_start_2286_, v_stop_2287_);
if (v___x_2288_ == 0)
{
lean_object* v___x_2289_; 
lean_dec(v_numParams_2271_);
lean_dec_ref(v_infos_2270_);
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v_b_2275_);
return v___x_2289_;
}
else
{
lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2317_; 
lean_inc(v_stop_2287_);
lean_inc(v_start_2286_);
lean_inc_ref(v_array_2285_);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_b_2275_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; lean_object* v_unused_2319_; lean_object* v_unused_2320_; 
v_unused_2318_ = lean_ctor_get(v_b_2275_, 2);
lean_dec(v_unused_2318_);
v_unused_2319_ = lean_ctor_get(v_b_2275_, 1);
lean_dec(v_unused_2319_);
v_unused_2320_ = lean_ctor_get(v_b_2275_, 0);
lean_dec(v_unused_2320_);
v___x_2291_ = v_b_2275_;
v_isShared_2292_ = v_isSharedCheck_2317_;
goto v_resetjp_2290_;
}
else
{
lean_dec(v_b_2275_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2317_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v_ctorSyntax_2294_; lean_object* v_a_2295_; lean_object* v_ctors_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2293_ = lean_array_fget_borrowed(v_array_2285_, v_start_2286_);
v_ctorSyntax_2294_ = lean_ctor_get(v___x_2293_, 4);
v_a_2295_ = lean_array_uget_borrowed(v_as_2272_, v_i_2274_);
v_ctors_2296_ = lean_ctor_get(v_a_2295_, 4);
v___x_2297_ = lean_array_get_size(v_ctorSyntax_2294_);
v___x_2298_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ctorSyntax_2294_);
v___x_2299_ = l_Array_toSubarray___redArg(v_ctorSyntax_2294_, v___x_2298_, v___x_2297_);
lean_inc(v_numParams_2271_);
lean_inc_ref(v_infos_2270_);
lean_inc(v_a_2295_);
v___x_2300_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2295_, v_infos_2270_, v_numParams_2271_, v_ctors_2296_, v___x_2299_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2300_) == 0)
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_dec_ref_known(v___x_2300_, 1);
v___x_2301_ = lean_unsigned_to_nat(1u);
v___x_2302_ = lean_nat_add(v_start_2286_, v___x_2301_);
lean_dec(v_start_2286_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v___x_2302_);
v___x_2304_ = v___x_2291_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_array_2285_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2302_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_stop_2287_);
v___x_2304_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
size_t v___x_2305_; size_t v___x_2306_; 
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_add(v_i_2274_, v___x_2305_);
v_i_2274_ = v___x_2306_;
v_b_2275_ = v___x_2304_;
goto _start;
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2291_);
lean_dec(v_stop_2287_);
lean_dec(v_start_2286_);
lean_dec_ref(v_array_2285_);
lean_dec(v_numParams_2271_);
lean_dec_ref(v_infos_2270_);
v_a_2309_ = lean_ctor_get(v___x_2300_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2300_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2300_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2300_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2321_, lean_object* v_numParams_2322_, lean_object* v_as_2323_, lean_object* v_sz_2324_, lean_object* v_i_2325_, lean_object* v_b_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
size_t v_sz_boxed_2334_; size_t v_i_boxed_2335_; lean_object* v_res_2336_; 
v_sz_boxed_2334_ = lean_unbox_usize(v_sz_2324_);
lean_dec(v_sz_2324_);
v_i_boxed_2335_ = lean_unbox_usize(v_i_2325_);
lean_dec(v_i_2325_);
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2321_, v_numParams_2322_, v_as_2323_, v_sz_boxed_2334_, v_i_boxed_2335_, v_b_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec_ref(v_as_2323_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2337_, lean_object* v_infos_2338_, lean_object* v_coinductiveElabData_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; size_t v_sz_2350_; size_t v___x_2351_; lean_object* v___x_2352_; 
v___x_2347_ = lean_unsigned_to_nat(0u);
v___x_2348_ = lean_array_get_size(v_coinductiveElabData_2339_);
v___x_2349_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2339_, v___x_2347_, v___x_2348_);
v_sz_2350_ = lean_array_size(v_infos_2338_);
v___x_2351_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2338_);
v___x_2352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2338_, v_numParams_2337_, v_infos_2338_, v_sz_2350_, v___x_2351_, v___x_2349_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
lean_dec_ref(v_infos_2338_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2360_; 
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v___x_2352_, 0);
lean_dec(v_unused_2361_);
v___x_2354_ = v___x_2352_;
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
else
{
lean_dec(v___x_2352_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2360_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_box(0);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2356_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2352_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2370_, lean_object* v_infos_2371_, lean_object* v_coinductiveElabData_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2370_, v_infos_2371_, v_coinductiveElabData_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2381_, lean_object* v_infos_2382_, lean_object* v_numParams_2383_, lean_object* v_as_2384_, lean_object* v_as_x27_2385_, lean_object* v_b_2386_, lean_object* v_a_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2381_, v_infos_2382_, v_numParams_2383_, v_as_x27_2385_, v_b_2386_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2396_, lean_object* v_infos_2397_, lean_object* v_numParams_2398_, lean_object* v_as_2399_, lean_object* v_as_x27_2400_, lean_object* v_b_2401_, lean_object* v_a_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2396_, v_infos_2397_, v_numParams_2398_, v_as_2399_, v_as_x27_2400_, v_b_2401_, v_a_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v_as_x27_2400_);
lean_dec(v_as_2399_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2411_, lean_object* v_msg_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_msg_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2421_, v_msg_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2431_, lean_object* v_macroStack_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2431_, v_macroStack_2432_, v___y_2437_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2441_, lean_object* v_macroStack_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2441_, v_macroStack_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_mvarId_2451_, lean_object* v_x_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2451_, v_x_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2458_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2458_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2458_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2458_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_mvarId_2475_, lean_object* v_x_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2475_, v_x_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2483_, lean_object* v_mvarId_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2484_, v_x_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2492_, lean_object* v_mvarId_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2492_, v_mvarId_2493_, v_x_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_type_2501_, lean_object* v_maxFVars_x3f_2502_, lean_object* v_k_2503_, uint8_t v_cleanupAnnotations_2504_, uint8_t v_whnfType_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___f_2511_; lean_object* v___x_2512_; 
v___f_2511_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2511_, 0, v_k_2503_);
v___x_2512_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2501_, v_maxFVars_x3f_2502_, v___f_2511_, v_cleanupAnnotations_2504_, v_whnfType_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
v_a_2521_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2512_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2512_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_type_2529_, lean_object* v_maxFVars_x3f_2530_, lean_object* v_k_2531_, lean_object* v_cleanupAnnotations_2532_, lean_object* v_whnfType_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2539_; uint8_t v_whnfType_boxed_2540_; lean_object* v_res_2541_; 
v_cleanupAnnotations_boxed_2539_ = lean_unbox(v_cleanupAnnotations_2532_);
v_whnfType_boxed_2540_ = lean_unbox(v_whnfType_2533_);
v_res_2541_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2529_, v_maxFVars_x3f_2530_, v_k_2531_, v_cleanupAnnotations_boxed_2539_, v_whnfType_boxed_2540_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2542_, lean_object* v_type_2543_, lean_object* v_maxFVars_x3f_2544_, lean_object* v_k_2545_, uint8_t v_cleanupAnnotations_2546_, uint8_t v_whnfType_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2543_, v_maxFVars_x3f_2544_, v_k_2545_, v_cleanupAnnotations_2546_, v_whnfType_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2554_, lean_object* v_type_2555_, lean_object* v_maxFVars_x3f_2556_, lean_object* v_k_2557_, lean_object* v_cleanupAnnotations_2558_, lean_object* v_whnfType_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2565_; uint8_t v_whnfType_boxed_2566_; lean_object* v_res_2567_; 
v_cleanupAnnotations_boxed_2565_ = lean_unbox(v_cleanupAnnotations_2558_);
v_whnfType_boxed_2566_ = lean_unbox(v_whnfType_2559_);
v_res_2567_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2554_, v_type_2555_, v_maxFVars_x3f_2556_, v_k_2557_, v_cleanupAnnotations_boxed_2565_, v_whnfType_boxed_2566_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2568_, lean_object* v_msg_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_fileName_2575_; lean_object* v_fileMap_2576_; lean_object* v_options_2577_; lean_object* v_currRecDepth_2578_; lean_object* v_maxRecDepth_2579_; lean_object* v_ref_2580_; lean_object* v_currNamespace_2581_; lean_object* v_openDecls_2582_; lean_object* v_initHeartbeats_2583_; lean_object* v_maxHeartbeats_2584_; lean_object* v_quotContext_2585_; lean_object* v_currMacroScope_2586_; uint8_t v_diag_2587_; lean_object* v_cancelTk_x3f_2588_; uint8_t v_suppressElabErrors_2589_; lean_object* v_inheritedTraceOptions_2590_; lean_object* v_ref_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v_fileName_2575_ = lean_ctor_get(v___y_2572_, 0);
v_fileMap_2576_ = lean_ctor_get(v___y_2572_, 1);
v_options_2577_ = lean_ctor_get(v___y_2572_, 2);
v_currRecDepth_2578_ = lean_ctor_get(v___y_2572_, 3);
v_maxRecDepth_2579_ = lean_ctor_get(v___y_2572_, 4);
v_ref_2580_ = lean_ctor_get(v___y_2572_, 5);
v_currNamespace_2581_ = lean_ctor_get(v___y_2572_, 6);
v_openDecls_2582_ = lean_ctor_get(v___y_2572_, 7);
v_initHeartbeats_2583_ = lean_ctor_get(v___y_2572_, 8);
v_maxHeartbeats_2584_ = lean_ctor_get(v___y_2572_, 9);
v_quotContext_2585_ = lean_ctor_get(v___y_2572_, 10);
v_currMacroScope_2586_ = lean_ctor_get(v___y_2572_, 11);
v_diag_2587_ = lean_ctor_get_uint8(v___y_2572_, sizeof(void*)*14);
v_cancelTk_x3f_2588_ = lean_ctor_get(v___y_2572_, 12);
v_suppressElabErrors_2589_ = lean_ctor_get_uint8(v___y_2572_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2590_ = lean_ctor_get(v___y_2572_, 13);
v_ref_2591_ = l_Lean_replaceRef(v_ref_2568_, v_ref_2580_);
lean_inc_ref(v_inheritedTraceOptions_2590_);
lean_inc(v_cancelTk_x3f_2588_);
lean_inc(v_currMacroScope_2586_);
lean_inc(v_quotContext_2585_);
lean_inc(v_maxHeartbeats_2584_);
lean_inc(v_initHeartbeats_2583_);
lean_inc(v_openDecls_2582_);
lean_inc(v_currNamespace_2581_);
lean_inc(v_maxRecDepth_2579_);
lean_inc(v_currRecDepth_2578_);
lean_inc_ref(v_options_2577_);
lean_inc_ref(v_fileMap_2576_);
lean_inc_ref(v_fileName_2575_);
v___x_2592_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2592_, 0, v_fileName_2575_);
lean_ctor_set(v___x_2592_, 1, v_fileMap_2576_);
lean_ctor_set(v___x_2592_, 2, v_options_2577_);
lean_ctor_set(v___x_2592_, 3, v_currRecDepth_2578_);
lean_ctor_set(v___x_2592_, 4, v_maxRecDepth_2579_);
lean_ctor_set(v___x_2592_, 5, v_ref_2591_);
lean_ctor_set(v___x_2592_, 6, v_currNamespace_2581_);
lean_ctor_set(v___x_2592_, 7, v_openDecls_2582_);
lean_ctor_set(v___x_2592_, 8, v_initHeartbeats_2583_);
lean_ctor_set(v___x_2592_, 9, v_maxHeartbeats_2584_);
lean_ctor_set(v___x_2592_, 10, v_quotContext_2585_);
lean_ctor_set(v___x_2592_, 11, v_currMacroScope_2586_);
lean_ctor_set(v___x_2592_, 12, v_cancelTk_x3f_2588_);
lean_ctor_set(v___x_2592_, 13, v_inheritedTraceOptions_2590_);
lean_ctor_set_uint8(v___x_2592_, sizeof(void*)*14, v_diag_2587_);
lean_ctor_set_uint8(v___x_2592_, sizeof(void*)*14 + 1, v_suppressElabErrors_2589_);
v___x_2593_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2569_, v___y_2570_, v___y_2571_, v___x_2592_, v___y_2573_);
lean_dec_ref_known(v___x_2592_, 14);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2594_, lean_object* v_msg_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2594_, v_msg_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v_ref_2594_);
return v_res_2601_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2602_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2603_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
return v___x_2604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_ctor_set(v___x_2607_, 2, v___x_2606_);
lean_ctor_set(v___x_2607_, 3, v___x_2606_);
lean_ctor_set(v___x_2607_, 4, v___x_2605_);
lean_ctor_set(v___x_2607_, 5, v___x_2605_);
lean_ctor_set(v___x_2607_, 6, v___x_2605_);
lean_ctor_set(v___x_2607_, 7, v___x_2605_);
lean_ctor_set(v___x_2607_, 8, v___x_2605_);
lean_ctor_set(v___x_2607_, 9, v___x_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_unsigned_to_nat(32u);
v___x_2609_ = lean_mk_empty_array_with_capacity(v___x_2608_);
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2611_ = ((size_t)5ULL);
v___x_2612_ = lean_unsigned_to_nat(0u);
v___x_2613_ = lean_unsigned_to_nat(32u);
v___x_2614_ = lean_mk_empty_array_with_capacity(v___x_2613_);
v___x_2615_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2616_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2614_);
lean_ctor_set(v___x_2616_, 2, v___x_2612_);
lean_ctor_set(v___x_2616_, 3, v___x_2612_);
lean_ctor_set_usize(v___x_2616_, 4, v___x_2611_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2617_ = lean_box(1);
v___x_2618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2618_);
lean_ctor_set(v___x_2620_, 2, v___x_2617_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2623_ = l_Lean_stringToMessageData(v___x_2622_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2626_ = l_Lean_stringToMessageData(v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2629_ = l_Lean_stringToMessageData(v___x_2628_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2635_ = l_Lean_stringToMessageData(v___x_2634_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2638_ = l_Lean_stringToMessageData(v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2642_, lean_object* v_declHint_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; lean_object* v_env_2647_; uint8_t v___x_2648_; 
v___x_2646_ = lean_st_ref_get(v___y_2644_);
v_env_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc_ref(v_env_2647_);
lean_dec(v___x_2646_);
v___x_2648_ = l_Lean_Name_isAnonymous(v_declHint_2643_);
if (v___x_2648_ == 0)
{
uint8_t v_isExporting_2649_; 
v_isExporting_2649_ = lean_ctor_get_uint8(v_env_2647_, sizeof(void*)*8);
if (v_isExporting_2649_ == 0)
{
lean_object* v___x_2650_; 
lean_dec_ref(v_env_2647_);
lean_dec(v_declHint_2643_);
v___x_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2650_, 0, v_msg_2642_);
return v___x_2650_;
}
else
{
lean_object* v___x_2651_; uint8_t v___x_2652_; 
lean_inc_ref(v_env_2647_);
v___x_2651_ = l_Lean_Environment_setExporting(v_env_2647_, v___x_2648_);
lean_inc(v_declHint_2643_);
lean_inc_ref(v___x_2651_);
v___x_2652_ = l_Lean_Environment_contains(v___x_2651_, v_declHint_2643_, v_isExporting_2649_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref(v___x_2651_);
lean_dec_ref(v_env_2647_);
lean_dec(v_declHint_2643_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_msg_2642_);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v_c_2659_; lean_object* v___x_2660_; 
v___x_2654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2655_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2656_ = l_Lean_Options_empty;
v___x_2657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2651_);
lean_ctor_set(v___x_2657_, 1, v___x_2654_);
lean_ctor_set(v___x_2657_, 2, v___x_2655_);
lean_ctor_set(v___x_2657_, 3, v___x_2656_);
lean_inc(v_declHint_2643_);
v___x_2658_ = l_Lean_MessageData_ofConstName(v_declHint_2643_, v___x_2648_);
v_c_2659_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2659_, 0, v___x_2657_);
lean_ctor_set(v_c_2659_, 1, v___x_2658_);
v___x_2660_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2647_, v_declHint_2643_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec_ref(v_env_2647_);
lean_dec(v_declHint_2643_);
v___x_2661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2661_);
lean_ctor_set(v___x_2662_, 1, v_c_2659_);
v___x_2663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2662_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = l_Lean_MessageData_note(v___x_2664_);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v_msg_2642_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2666_);
return v___x_2667_;
}
else
{
lean_object* v_val_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2703_; 
v_val_2668_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2670_ = v___x_2660_;
v_isShared_2671_ = v_isSharedCheck_2703_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_val_2668_);
lean_dec(v___x_2660_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2703_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v_mod_2675_; uint8_t v___x_2676_; 
v___x_2672_ = lean_box(0);
v___x_2673_ = l_Lean_Environment_header(v_env_2647_);
lean_dec_ref(v_env_2647_);
v___x_2674_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2673_);
v_mod_2675_ = lean_array_get(v___x_2672_, v___x_2674_, v_val_2668_);
lean_dec(v_val_2668_);
lean_dec_ref(v___x_2674_);
v___x_2676_ = l_Lean_isPrivateName(v_declHint_2643_);
lean_dec(v_declHint_2643_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; 
v___x_2677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2677_);
lean_ctor_set(v___x_2678_, 1, v_c_2659_);
v___x_2679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2678_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_MessageData_ofName(v_mod_2675_);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = l_Lean_MessageData_note(v___x_2684_);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_msg_2642_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2686_);
v___x_2688_ = v___x_2670_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
lean_ctor_set(v___x_2691_, 1, v_c_2659_);
v___x_2692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_Lean_MessageData_ofName(v_mod_2675_);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_MessageData_note(v___x_2697_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v_msg_2642_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set_tag(v___x_2670_, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2699_);
v___x_2701_ = v___x_2670_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2704_; 
lean_dec_ref(v_env_2647_);
lean_dec(v_declHint_2643_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v_msg_2642_);
return v___x_2704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2705_, lean_object* v_declHint_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2705_, v_declHint_2706_, v___y_2707_);
lean_dec(v___y_2707_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2710_, lean_object* v_declHint_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2727_; 
v___x_2717_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2710_, v_declHint_2711_, v___y_2715_);
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2727_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2722_ = l_Lean_unknownIdentifierMessageTag;
v___x_2723_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2722_);
lean_ctor_set(v___x_2723_, 1, v_a_2718_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2723_);
v___x_2725_ = v___x_2720_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2728_, lean_object* v_declHint_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2728_, v_declHint_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2736_, lean_object* v_msg_2737_, lean_object* v_declHint_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; lean_object* v_a_2745_; lean_object* v___x_2746_; 
v___x_2744_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2737_, v_declHint_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2736_, v_a_2745_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2747_, lean_object* v_msg_2748_, lean_object* v_declHint_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2747_, v_msg_2748_, v_declHint_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v_ref_2747_);
return v_res_2755_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2758_ = l_Lean_stringToMessageData(v___x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2759_, lean_object* v_constName_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2766_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2767_ = 0;
lean_inc(v_constName_2760_);
v___x_2768_ = l_Lean_MessageData_ofConstName(v_constName_2760_, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2766_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2759_, v___x_2771_, v_constName_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2773_, lean_object* v_constName_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2773_, v_constName_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v_ref_2773_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_ref_2787_; lean_object* v___x_2788_; 
v_ref_2787_ = lean_ctor_get(v___y_2784_, 5);
v___x_2788_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2787_, v_constName_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v_env_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; 
v___x_2802_ = lean_st_ref_get(v___y_2800_);
v_env_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_env_2803_);
lean_dec(v___x_2802_);
v___x_2804_ = 0;
lean_inc(v_constName_2796_);
v___x_2805_ = l_Lean_Environment_find_x3f(v_env_2803_, v_constName_2796_, v___x_2804_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v___x_2806_; 
v___x_2806_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2806_;
}
else
{
lean_object* v_val_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec(v_constName_2796_);
v_val_2807_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2805_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_val_2807_);
lean_dec(v___x_2805_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set_tag(v___x_2809_, 0);
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_val_2807_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
return v_res_2821_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2822_, lean_object* v_as_2823_, size_t v_i_2824_, size_t v_stop_2825_){
_start:
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_usize_dec_eq(v_i_2824_, v_stop_2825_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = lean_array_uget_borrowed(v_as_2823_, v_i_2824_);
v___x_2828_ = l_Lean_Expr_isAppOf(v_e_2822_, v___x_2827_);
if (v___x_2828_ == 0)
{
size_t v___x_2829_; size_t v___x_2830_; 
v___x_2829_ = ((size_t)1ULL);
v___x_2830_ = lean_usize_add(v_i_2824_, v___x_2829_);
v_i_2824_ = v___x_2830_;
goto _start;
}
else
{
return v___x_2828_;
}
}
else
{
uint8_t v___x_2832_; 
v___x_2832_ = 0;
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2833_, lean_object* v_as_2834_, lean_object* v_i_2835_, lean_object* v_stop_2836_){
_start:
{
size_t v_i_boxed_2837_; size_t v_stop_boxed_2838_; uint8_t v_res_2839_; lean_object* v_r_2840_; 
v_i_boxed_2837_ = lean_unbox_usize(v_i_2835_);
lean_dec(v_i_2835_);
v_stop_boxed_2838_ = lean_unbox_usize(v_stop_2836_);
lean_dec(v_stop_2836_);
v_res_2839_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2833_, v_as_2834_, v_i_boxed_2837_, v_stop_boxed_2838_);
lean_dec_ref(v_as_2834_);
lean_dec_ref(v_e_2833_);
v_r_2840_ = lean_box(v_res_2839_);
return v_r_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2841_, lean_object* v_name_2842_, lean_object* v_levels_2843_, lean_object* v_params_2844_, lean_object* v___y_2845_, lean_object* v___x_2846_, lean_object* v_e_2847_){
_start:
{
uint8_t v___x_2848_; 
v___x_2848_ = l_Lean_Expr_isApp(v_e_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref(v_e_2847_);
lean_dec_ref(v_params_2844_);
lean_dec(v_levels_2843_);
lean_dec(v_name_2842_);
lean_dec(v_numParams_2841_);
v___x_2849_ = lean_box(0);
return v___x_2849_;
}
else
{
lean_object* v_dummy_2850_; lean_object* v_nargs_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___y_2859_; uint8_t v___x_2869_; 
v_dummy_2850_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2851_ = l_Lean_Expr_getAppNumArgs(v_e_2847_);
lean_inc(v_nargs_2851_);
v___x_2852_ = lean_mk_array(v_nargs_2851_, v_dummy_2850_);
v___x_2853_ = lean_unsigned_to_nat(1u);
v___x_2854_ = lean_nat_sub(v_nargs_2851_, v___x_2853_);
lean_dec(v_nargs_2851_);
lean_inc_ref(v_e_2847_);
v___x_2855_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2847_, v___x_2852_, v___x_2854_);
v___x_2856_ = lean_array_get_size(v___x_2855_);
v___x_2857_ = l_Array_toSubarray___redArg(v___x_2855_, v_numParams_2841_, v___x_2856_);
v___x_2869_ = l_Lean_Expr_isAppOf(v_e_2847_, v_name_2842_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
lean_dec(v_name_2842_);
v___x_2870_ = lean_array_get_size(v___y_2845_);
v___x_2871_ = lean_nat_dec_lt(v___x_2846_, v___x_2870_);
if (v___x_2871_ == 0)
{
v___y_2859_ = v___x_2869_;
goto v___jp_2858_;
}
else
{
if (v___x_2871_ == 0)
{
v___y_2859_ = v___x_2869_;
goto v___jp_2858_;
}
else
{
size_t v___x_2872_; size_t v___x_2873_; uint8_t v___x_2874_; 
v___x_2872_ = ((size_t)0ULL);
v___x_2873_ = lean_usize_of_nat(v___x_2870_);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2847_, v___y_2845_, v___x_2872_, v___x_2873_);
v___y_2859_ = v___x_2874_;
goto v___jp_2858_;
}
}
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
lean_dec_ref(v_e_2847_);
v___x_2875_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2842_);
v___x_2876_ = l_Lean_mkConst(v___x_2875_, v_levels_2843_);
v___x_2877_ = l_Subarray_copy___redArg(v___x_2857_);
v___x_2878_ = l_Array_append___redArg(v_params_2844_, v___x_2877_);
lean_dec_ref(v___x_2877_);
v___x_2879_ = l_Lean_mkAppN(v___x_2876_, v___x_2878_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
return v___x_2880_;
}
v___jp_2858_:
{
if (v___y_2859_ == 0)
{
lean_object* v___x_2860_; 
lean_dec_ref(v___x_2857_);
lean_dec_ref(v_e_2847_);
lean_dec_ref(v_params_2844_);
lean_dec(v_levels_2843_);
v___x_2860_ = lean_box(0);
return v___x_2860_;
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2861_ = l_Lean_Expr_getAppFn(v_e_2847_);
lean_dec_ref(v_e_2847_);
v___x_2862_ = l_Lean_Expr_constName(v___x_2861_);
lean_dec_ref(v___x_2861_);
v___x_2863_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2862_);
v___x_2864_ = l_Lean_mkConst(v___x_2863_, v_levels_2843_);
v___x_2865_ = l_Subarray_copy___redArg(v___x_2857_);
v___x_2866_ = l_Array_append___redArg(v_params_2844_, v___x_2865_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2881_, lean_object* v_name_2882_, lean_object* v_levels_2883_, lean_object* v_params_2884_, lean_object* v___y_2885_, lean_object* v___x_2886_, lean_object* v_e_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2881_, v_name_2882_, v_levels_2883_, v_params_2884_, v___y_2885_, v___x_2886_, v_e_2887_);
lean_dec(v___x_2886_);
lean_dec_ref(v___y_2885_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v_eqProof_2889_, lean_object* v___x_2890_, lean_object* v_eNew_2891_, lean_object* v_snd_2892_, lean_object* v___x_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_Meta_mkEqMP(v_eqProof_2889_, v___x_2890_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2901_, 0, v_eNew_2891_);
v___x_2902_ = lean_box(0);
v___x_2903_ = l_Lean_MVarId_replace(v_snd_2892_, v___x_2893_, v_a_2900_, v___x_2901_, v___x_2902_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
return v___x_2903_;
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v___x_2893_);
lean_dec(v_snd_2892_);
lean_dec_ref(v_eNew_2891_);
v_a_2904_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2899_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2899_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object* v_eqProof_2912_, lean_object* v___x_2913_, lean_object* v_eNew_2914_, lean_object* v_snd_2915_, lean_object* v___x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_2912_, v___x_2913_, v_eNew_2914_, v_snd_2915_, v___x_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2922_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0));
v___x_2925_ = l_Lean_stringToMessageData(v___x_2924_);
return v___x_2925_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9));
v___x_2948_ = l_Lean_stringToMessageData(v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_2949_, lean_object* v___x_2950_, uint8_t v___x_2951_, lean_object* v___x_2952_, lean_object* v___x_2953_, uint8_t v___x_2954_, lean_object* v___x_2955_, lean_object* v_params_2956_, lean_object* v_args_2957_, lean_object* v_indices_2958_, uint8_t v___x_2959_, lean_object* v___x_2960_, lean_object* v_a_2961_, lean_object* v___x_2962_, lean_object* v___f_2963_, lean_object* v___x_2964_, lean_object* v_targetArgs_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = lean_array_get_size(v_targetArgs_2965_);
v___x_2973_ = lean_nat_dec_eq(v___x_2972_, v___x_2949_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
lean_dec_ref(v___x_2953_);
lean_dec(v___x_2952_);
lean_dec_ref(v___x_2950_);
v___x_2974_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_2975_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_2974_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
return v___x_2975_;
}
else
{
lean_object* v___x_2976_; 
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v___x_2950_);
v___x_2976_ = lean_infer_type(v___x_2950_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref_known(v___x_2976_, 1);
if (lean_obj_tag(v_a_2977_) == 7)
{
lean_object* v_binderType_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_binderType_2978_ = lean_ctor_get(v_a_2977_, 1);
lean_inc_ref(v_binderType_2978_);
lean_dec_ref_known(v_a_2977_, 3);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_binderType_2978_);
v___x_2980_ = l_Lean_Meta_mkFreshExprMVar(v___x_2979_, v___x_2951_, v___x_2952_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = l_Lean_Expr_mvarId_x21(v_a_2981_);
v___x_2983_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2982_, v___x_2953_, v___x_2954_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = lean_array_fget_borrowed(v_targetArgs_2965_, v___x_2955_);
lean_inc(v___x_2985_);
v___x_2986_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2984_, v___x_2985_, v___y_2968_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3068_; 
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v___x_2986_, 0);
lean_dec(v_unused_3069_);
v___x_2988_ = v___x_2986_;
v_isShared_2989_ = v_isSharedCheck_3068_;
goto v_resetjp_2987_;
}
else
{
lean_dec(v___x_2986_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3068_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2990_ = l_Lean_Expr_app___override(v___x_2950_, v_a_2981_);
lean_inc_ref(v_params_2956_);
v___x_2991_ = l_Array_append___redArg(v_params_2956_, v_args_2957_);
v___x_2992_ = l_Array_append___redArg(v___x_2991_, v_indices_2958_);
v___x_2993_ = l_Array_append___redArg(v___x_2992_, v_targetArgs_2965_);
v___x_2994_ = 1;
v___x_2995_ = l_Lean_Meta_mkLambdaFVars(v___x_2993_, v___x_2990_, v___x_2959_, v___x_2954_, v___x_2959_, v___x_2954_, v___x_2994_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec_ref(v___x_2993_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2997_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_2996_, v___y_2968_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = l_Lean_Meta_mkForallFVars(v_params_2956_, v___x_2960_, v___x_2959_, v___x_2954_, v___x_2954_, v___x_2994_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec_ref(v_params_2956_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = l_Lean_ConstantInfo_levelParams(v_a_2961_);
v___x_3002_ = l_Lean_mkCasesOnName(v___x_2962_);
v___x_3003_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3004_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_3002_, v___x_3001_, v_a_3000_, v_a_2998_, v___x_3003_, v___y_2970_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
if (v_isShared_2989_ == 0)
{
lean_ctor_set_tag(v___x_2988_, 1);
lean_ctor_set(v___x_2988_, 0, v_a_3005_);
v___x_3007_ = v___x_2988_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3005_);
v___x_3007_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_addDecl(v___x_3007_, v___x_2959_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
lean_dec_ref_known(v___x_3008_, 1);
v___x_3009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8));
v___x_3010_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3010_, 0, v___x_3002_);
lean_closure_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_box(1);
v___x_3014_ = lean_mk_empty_array_with_capacity(v___x_2955_);
v___x_3015_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3015_, 0, v___x_3011_);
lean_ctor_set(v___x_3015_, 1, v___x_3012_);
lean_ctor_set(v___x_3015_, 2, v___x_3011_);
lean_ctor_set(v___x_3015_, 3, v___f_2963_);
lean_ctor_set(v___x_3015_, 4, v___x_3013_);
lean_ctor_set(v___x_3015_, 5, v___x_3013_);
lean_ctor_set(v___x_3015_, 6, v___x_3011_);
lean_ctor_set(v___x_3015_, 7, v___x_3014_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8, v___x_2954_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 1, v___x_2954_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 2, v___x_2954_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 3, v___x_2954_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 4, v___x_2959_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 5, v___x_2959_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 6, v___x_2959_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 7, v___x_2959_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 8, v___x_2954_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 9, v___x_2959_);
lean_ctor_set_uint8(v___x_3015_, sizeof(void*)*8 + 10, v___x_2954_);
v___x_3016_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3016_, 0, v___x_2964_);
lean_ctor_set(v___x_3016_, 1, v___x_3013_);
lean_ctor_set(v___x_3016_, 2, v___x_3012_);
lean_ctor_set(v___x_3016_, 3, v___x_3012_);
lean_ctor_set(v___x_3016_, 4, v___x_3012_);
lean_ctor_set(v___x_3016_, 5, v___x_3013_);
lean_ctor_set(v___x_3016_, 6, v___x_3012_);
v___x_3017_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3010_, v___x_3015_, v___x_3016_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3026_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3020_ = v___x_3017_;
v_isShared_3021_ = v_isSharedCheck_3026_;
goto v_resetjp_3019_;
}
else
{
lean_inc(v_a_3018_);
lean_dec(v___x_3017_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3026_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v_fst_3022_; lean_object* v___x_3024_; 
v_fst_3022_ = lean_ctor_get(v_a_3018_, 0);
lean_inc(v_fst_3022_);
lean_dec(v_a_3018_);
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v_fst_3022_);
v___x_3024_ = v___x_3020_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_fst_3022_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
v_a_3027_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3017_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3017_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_dec(v___x_3002_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
return v___x_3008_;
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v___x_3002_);
lean_del_object(v___x_2988_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
v_a_3036_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3004_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3004_);
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
lean_dec(v_a_2998_);
lean_del_object(v___x_2988_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
v_a_3044_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2999_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2999_);
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
lean_del_object(v___x_2988_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
v_a_3052_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_2997_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_2997_);
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
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_del_object(v___x_2988_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
v_a_3060_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_2995_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_2995_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
}
else
{
lean_dec(v_a_2981_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
lean_dec_ref(v___x_2950_);
return v___x_2986_;
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v_a_2981_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
lean_dec_ref(v___x_2950_);
v_a_3070_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2983_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2983_);
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
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
lean_dec_ref(v___x_2953_);
lean_dec_ref(v___x_2950_);
v_a_3078_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2980_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2980_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec(v_a_2977_);
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
lean_dec_ref(v___x_2953_);
lean_dec(v___x_2952_);
lean_dec_ref(v___x_2950_);
v___x_3086_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3087_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3086_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
return v___x_3087_;
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v___x_2964_);
lean_dec_ref(v___f_2963_);
lean_dec(v___x_2962_);
lean_dec_ref(v___x_2960_);
lean_dec_ref(v_params_2956_);
lean_dec_ref(v___x_2953_);
lean_dec(v___x_2952_);
lean_dec_ref(v___x_2950_);
v_a_3088_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_2976_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_2976_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3096_ = _args[0];
lean_object* v___x_3097_ = _args[1];
lean_object* v___x_3098_ = _args[2];
lean_object* v___x_3099_ = _args[3];
lean_object* v___x_3100_ = _args[4];
lean_object* v___x_3101_ = _args[5];
lean_object* v___x_3102_ = _args[6];
lean_object* v_params_3103_ = _args[7];
lean_object* v_args_3104_ = _args[8];
lean_object* v_indices_3105_ = _args[9];
lean_object* v___x_3106_ = _args[10];
lean_object* v___x_3107_ = _args[11];
lean_object* v_a_3108_ = _args[12];
lean_object* v___x_3109_ = _args[13];
lean_object* v___f_3110_ = _args[14];
lean_object* v___x_3111_ = _args[15];
lean_object* v_targetArgs_3112_ = _args[16];
lean_object* v_x_3113_ = _args[17];
lean_object* v___y_3114_ = _args[18];
lean_object* v___y_3115_ = _args[19];
lean_object* v___y_3116_ = _args[20];
lean_object* v___y_3117_ = _args[21];
lean_object* v___y_3118_ = _args[22];
_start:
{
uint8_t v___x_16827__boxed_3119_; uint8_t v___x_16830__boxed_3120_; uint8_t v___x_16832__boxed_3121_; lean_object* v_res_3122_; 
v___x_16827__boxed_3119_ = lean_unbox(v___x_3098_);
v___x_16830__boxed_3120_ = lean_unbox(v___x_3101_);
v___x_16832__boxed_3121_ = lean_unbox(v___x_3106_);
v_res_3122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3096_, v___x_3097_, v___x_16827__boxed_3119_, v___x_3099_, v___x_3100_, v___x_16830__boxed_3120_, v___x_3102_, v_params_3103_, v_args_3104_, v_indices_3105_, v___x_16832__boxed_3121_, v___x_3107_, v_a_3108_, v___x_3109_, v___f_3110_, v___x_3111_, v_targetArgs_3112_, v_x_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec_ref(v_x_3113_);
lean_dec_ref(v_targetArgs_3112_);
lean_dec_ref(v_a_3108_);
lean_dec_ref(v_indices_3105_);
lean_dec_ref(v_args_3104_);
lean_dec(v___x_3102_);
lean_dec(v___x_3096_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3123_, lean_object* v___x_3124_, uint8_t v___x_3125_, lean_object* v___x_3126_, lean_object* v___x_3127_, uint8_t v___x_3128_, lean_object* v___x_3129_, lean_object* v_params_3130_, lean_object* v_args_3131_, uint8_t v___x_3132_, lean_object* v___x_3133_, lean_object* v_a_3134_, lean_object* v___x_3135_, lean_object* v___f_3136_, lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v_indices_3139_, lean_object* v_goalType_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___f_3150_; lean_object* v___x_3151_; 
v___x_3146_ = l_Lean_mkAppN(v___x_3123_, v_indices_3139_);
v___x_3147_ = lean_box(v___x_3125_);
v___x_3148_ = lean_box(v___x_3128_);
v___x_3149_ = lean_box(v___x_3132_);
v___f_3150_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 23, 16);
lean_closure_set(v___f_3150_, 0, v___x_3124_);
lean_closure_set(v___f_3150_, 1, v___x_3146_);
lean_closure_set(v___f_3150_, 2, v___x_3147_);
lean_closure_set(v___f_3150_, 3, v___x_3126_);
lean_closure_set(v___f_3150_, 4, v___x_3127_);
lean_closure_set(v___f_3150_, 5, v___x_3148_);
lean_closure_set(v___f_3150_, 6, v___x_3129_);
lean_closure_set(v___f_3150_, 7, v_params_3130_);
lean_closure_set(v___f_3150_, 8, v_args_3131_);
lean_closure_set(v___f_3150_, 9, v_indices_3139_);
lean_closure_set(v___f_3150_, 10, v___x_3149_);
lean_closure_set(v___f_3150_, 11, v___x_3133_);
lean_closure_set(v___f_3150_, 12, v_a_3134_);
lean_closure_set(v___f_3150_, 13, v___x_3135_);
lean_closure_set(v___f_3150_, 14, v___f_3136_);
lean_closure_set(v___f_3150_, 15, v___x_3137_);
v___x_3151_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3140_, v___x_3138_, v___f_3150_, v___x_3132_, v___x_3132_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
return v___x_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3152_ = _args[0];
lean_object* v___x_3153_ = _args[1];
lean_object* v___x_3154_ = _args[2];
lean_object* v___x_3155_ = _args[3];
lean_object* v___x_3156_ = _args[4];
lean_object* v___x_3157_ = _args[5];
lean_object* v___x_3158_ = _args[6];
lean_object* v_params_3159_ = _args[7];
lean_object* v_args_3160_ = _args[8];
lean_object* v___x_3161_ = _args[9];
lean_object* v___x_3162_ = _args[10];
lean_object* v_a_3163_ = _args[11];
lean_object* v___x_3164_ = _args[12];
lean_object* v___f_3165_ = _args[13];
lean_object* v___x_3166_ = _args[14];
lean_object* v___x_3167_ = _args[15];
lean_object* v_indices_3168_ = _args[16];
lean_object* v_goalType_3169_ = _args[17];
lean_object* v___y_3170_ = _args[18];
lean_object* v___y_3171_ = _args[19];
lean_object* v___y_3172_ = _args[20];
lean_object* v___y_3173_ = _args[21];
lean_object* v___y_3174_ = _args[22];
_start:
{
uint8_t v___x_17163__boxed_3175_; uint8_t v___x_17166__boxed_3176_; uint8_t v___x_17168__boxed_3177_; lean_object* v_res_3178_; 
v___x_17163__boxed_3175_ = lean_unbox(v___x_3154_);
v___x_17166__boxed_3176_ = lean_unbox(v___x_3157_);
v___x_17168__boxed_3177_ = lean_unbox(v___x_3161_);
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3152_, v___x_3153_, v___x_17163__boxed_3175_, v___x_3155_, v___x_3156_, v___x_17166__boxed_3176_, v___x_3158_, v_params_3159_, v_args_3160_, v___x_17168__boxed_3177_, v___x_3162_, v_a_3163_, v___x_3164_, v___f_3165_, v___x_3166_, v___x_3167_, v_indices_3168_, v_goalType_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object* v___x_3179_, uint8_t v___x_3180_, lean_object* v_snd_3181_, lean_object* v___x_3182_, uint8_t v___x_3183_, lean_object* v___x_3184_, lean_object* v___x_3185_, lean_object* v_a_3186_, lean_object* v___x_3187_, uint8_t v___x_3188_, lean_object* v___x_3189_, lean_object* v___x_3190_, lean_object* v_params_3191_, lean_object* v_args_3192_, lean_object* v___x_3193_, lean_object* v_a_3194_, lean_object* v___x_3195_, lean_object* v___f_3196_, lean_object* v___x_3197_, lean_object* v___x_3198_, lean_object* v_numIndices_3199_, lean_object* v_goalType_3200_, lean_object* v___x_3201_, lean_object* v___x_3202_, lean_object* v_fst_3203_, lean_object* v___x_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_lctx_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_lctx_3210_ = lean_ctor_get(v___y_3205_, 2);
lean_inc(v___x_3179_);
lean_inc_ref(v_lctx_3210_);
v___x_3211_ = l_Lean_LocalContext_get_x21(v_lctx_3210_, v___x_3179_);
v___x_3212_ = l_Lean_LocalDecl_type(v___x_3211_);
lean_dec_ref(v___x_3211_);
v___x_3213_ = 2;
v___x_3214_ = lean_box(0);
v___x_3215_ = 0;
v___x_3216_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3216_, 0, v___x_3214_);
lean_ctor_set_uint8(v___x_3216_, sizeof(void*)*1, v___x_3213_);
lean_ctor_set_uint8(v___x_3216_, sizeof(void*)*1 + 1, v___x_3180_);
lean_ctor_set_uint8(v___x_3216_, sizeof(void*)*1 + 2, v___x_3215_);
lean_inc_ref(v___x_3182_);
lean_inc(v_snd_3181_);
v___x_3217_ = l_Lean_MVarId_rewrite(v_snd_3181_, v___x_3212_, v___x_3182_, v___x_3180_, v___x_3216_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v_eNew_3219_; lean_object* v_eqProof_3220_; lean_object* v___x_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v_eNew_3219_ = lean_ctor_get(v_a_3218_, 0);
lean_inc_ref(v_eNew_3219_);
v_eqProof_3220_ = lean_ctor_get(v_a_3218_, 1);
lean_inc_ref(v_eqProof_3220_);
lean_dec(v_a_3218_);
lean_inc(v___x_3179_);
v___x_3221_ = l_Lean_mkFVar(v___x_3179_);
lean_inc(v_snd_3181_);
v___f_3222_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3222_, 0, v_eqProof_3220_);
lean_closure_set(v___f_3222_, 1, v___x_3221_);
lean_closure_set(v___f_3222_, 2, v_eNew_3219_);
lean_closure_set(v___f_3222_, 3, v_snd_3181_);
lean_closure_set(v___f_3222_, 4, v___x_3179_);
v___x_3223_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3181_, v___f_3222_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v___y_3226_; uint8_t v___x_3254_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v___x_3254_ = lean_nat_dec_lt(v___x_3201_, v___x_3202_);
if (v___x_3254_ == 0)
{
v___y_3226_ = v_fst_3203_;
goto v___jp_3225_;
}
else
{
lean_object* v_fvarId_3255_; lean_object* v_xs_x27_3256_; lean_object* v___x_3257_; 
v_fvarId_3255_ = lean_ctor_get(v_a_3224_, 0);
v_xs_x27_3256_ = lean_array_fset(v_fst_3203_, v___x_3201_, v___x_3204_);
lean_inc(v_fvarId_3255_);
v___x_3257_ = lean_array_fset(v_xs_x27_3256_, v___x_3201_, v_fvarId_3255_);
v___y_3226_ = v___x_3257_;
goto v___jp_3225_;
}
v___jp_3225_:
{
lean_object* v_mvarId_3227_; lean_object* v___x_3228_; 
v_mvarId_3227_ = lean_ctor_get(v_a_3224_, 1);
lean_inc(v_mvarId_3227_);
lean_dec(v_a_3224_);
v___x_3228_ = l_Lean_MVarId_revert(v_mvarId_3227_, v___y_3226_, v___x_3183_, v___x_3183_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v_a_3229_; lean_object* v_snd_3230_; lean_object* v___x_3231_; 
v_a_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_a_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v_snd_3230_ = lean_ctor_get(v_a_3229_, 1);
lean_inc(v_snd_3230_);
lean_dec(v_a_3229_);
v___x_3231_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3230_, v___x_3184_, v___y_3206_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3244_; 
v_isSharedCheck_3244_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3244_ == 0)
{
lean_object* v_unused_3245_; 
v_unused_3245_ = lean_ctor_get(v___x_3231_, 0);
lean_dec(v_unused_3245_);
v___x_3233_ = v___x_3231_;
v_isShared_3234_ = v_isSharedCheck_3244_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3231_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3244_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___f_3239_; lean_object* v___x_3241_; 
v___x_3235_ = l_Lean_Expr_app___override(v___x_3185_, v_a_3186_);
v___x_3236_ = lean_box(v___x_3188_);
v___x_3237_ = lean_box(v___x_3180_);
v___x_3238_ = lean_box(v___x_3183_);
v___f_3239_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 23, 16);
lean_closure_set(v___f_3239_, 0, v___x_3235_);
lean_closure_set(v___f_3239_, 1, v___x_3187_);
lean_closure_set(v___f_3239_, 2, v___x_3236_);
lean_closure_set(v___f_3239_, 3, v___x_3189_);
lean_closure_set(v___f_3239_, 4, v___x_3182_);
lean_closure_set(v___f_3239_, 5, v___x_3237_);
lean_closure_set(v___f_3239_, 6, v___x_3190_);
lean_closure_set(v___f_3239_, 7, v_params_3191_);
lean_closure_set(v___f_3239_, 8, v_args_3192_);
lean_closure_set(v___f_3239_, 9, v___x_3238_);
lean_closure_set(v___f_3239_, 10, v___x_3193_);
lean_closure_set(v___f_3239_, 11, v_a_3194_);
lean_closure_set(v___f_3239_, 12, v___x_3195_);
lean_closure_set(v___f_3239_, 13, v___f_3196_);
lean_closure_set(v___f_3239_, 14, v___x_3197_);
lean_closure_set(v___f_3239_, 15, v___x_3198_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 1);
lean_ctor_set(v___x_3233_, 0, v_numIndices_3199_);
v___x_3241_ = v___x_3233_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_numIndices_3199_);
v___x_3241_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3200_, v___x_3241_, v___f_3239_, v___x_3183_, v___x_3183_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
lean_dec_ref(v___y_3205_);
return v___x_3242_;
}
}
}
else
{
lean_dec_ref(v___y_3205_);
lean_dec_ref(v_goalType_3200_);
lean_dec(v_numIndices_3199_);
lean_dec(v___x_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v___f_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_a_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_args_3192_);
lean_dec_ref(v_params_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec(v___x_3187_);
lean_dec_ref(v_a_3186_);
lean_dec_ref(v___x_3185_);
lean_dec_ref(v___x_3182_);
return v___x_3231_;
}
}
else
{
lean_object* v_a_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3253_; 
lean_dec_ref(v___y_3205_);
lean_dec_ref(v_goalType_3200_);
lean_dec(v_numIndices_3199_);
lean_dec(v___x_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v___f_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_a_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_args_3192_);
lean_dec_ref(v_params_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec(v___x_3187_);
lean_dec_ref(v_a_3186_);
lean_dec_ref(v___x_3185_);
lean_dec_ref(v___x_3184_);
lean_dec_ref(v___x_3182_);
v_a_3246_ = lean_ctor_get(v___x_3228_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3248_ = v___x_3228_;
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_a_3246_);
lean_dec(v___x_3228_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3253_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
lean_object* v___x_3251_; 
if (v_isShared_3249_ == 0)
{
v___x_3251_ = v___x_3248_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_a_3246_);
v___x_3251_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
return v___x_3251_;
}
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v___y_3205_);
lean_dec_ref(v_fst_3203_);
lean_dec_ref(v_goalType_3200_);
lean_dec(v_numIndices_3199_);
lean_dec(v___x_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v___f_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_a_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_args_3192_);
lean_dec_ref(v_params_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec(v___x_3187_);
lean_dec_ref(v_a_3186_);
lean_dec_ref(v___x_3185_);
lean_dec_ref(v___x_3184_);
lean_dec_ref(v___x_3182_);
v_a_3258_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3223_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3223_);
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
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v___y_3205_);
lean_dec_ref(v_fst_3203_);
lean_dec_ref(v_goalType_3200_);
lean_dec(v_numIndices_3199_);
lean_dec(v___x_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v___f_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_a_3194_);
lean_dec_ref(v___x_3193_);
lean_dec_ref(v_args_3192_);
lean_dec_ref(v_params_3191_);
lean_dec(v___x_3190_);
lean_dec(v___x_3189_);
lean_dec(v___x_3187_);
lean_dec_ref(v_a_3186_);
lean_dec_ref(v___x_3185_);
lean_dec_ref(v___x_3184_);
lean_dec_ref(v___x_3182_);
lean_dec(v_snd_3181_);
lean_dec(v___x_3179_);
v_a_3266_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3217_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3217_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object** _args){
lean_object* v___x_3274_ = _args[0];
lean_object* v___x_3275_ = _args[1];
lean_object* v_snd_3276_ = _args[2];
lean_object* v___x_3277_ = _args[3];
lean_object* v___x_3278_ = _args[4];
lean_object* v___x_3279_ = _args[5];
lean_object* v___x_3280_ = _args[6];
lean_object* v_a_3281_ = _args[7];
lean_object* v___x_3282_ = _args[8];
lean_object* v___x_3283_ = _args[9];
lean_object* v___x_3284_ = _args[10];
lean_object* v___x_3285_ = _args[11];
lean_object* v_params_3286_ = _args[12];
lean_object* v_args_3287_ = _args[13];
lean_object* v___x_3288_ = _args[14];
lean_object* v_a_3289_ = _args[15];
lean_object* v___x_3290_ = _args[16];
lean_object* v___f_3291_ = _args[17];
lean_object* v___x_3292_ = _args[18];
lean_object* v___x_3293_ = _args[19];
lean_object* v_numIndices_3294_ = _args[20];
lean_object* v_goalType_3295_ = _args[21];
lean_object* v___x_3296_ = _args[22];
lean_object* v___x_3297_ = _args[23];
lean_object* v_fst_3298_ = _args[24];
lean_object* v___x_3299_ = _args[25];
lean_object* v___y_3300_ = _args[26];
lean_object* v___y_3301_ = _args[27];
lean_object* v___y_3302_ = _args[28];
lean_object* v___y_3303_ = _args[29];
lean_object* v___y_3304_ = _args[30];
_start:
{
uint8_t v___x_17231__boxed_3305_; uint8_t v___x_17234__boxed_3306_; uint8_t v___x_17239__boxed_3307_; lean_object* v_res_3308_; 
v___x_17231__boxed_3305_ = lean_unbox(v___x_3275_);
v___x_17234__boxed_3306_ = lean_unbox(v___x_3278_);
v___x_17239__boxed_3307_ = lean_unbox(v___x_3283_);
v_res_3308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3274_, v___x_17231__boxed_3305_, v_snd_3276_, v___x_3277_, v___x_17234__boxed_3306_, v___x_3279_, v___x_3280_, v_a_3281_, v___x_3282_, v___x_17239__boxed_3307_, v___x_3284_, v___x_3285_, v_params_3286_, v_args_3287_, v___x_3288_, v_a_3289_, v___x_3290_, v___f_3291_, v___x_3292_, v___x_3293_, v_numIndices_3294_, v_goalType_3295_, v___x_3296_, v___x_3297_, v_fst_3298_, v___x_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
lean_dec(v___x_3297_);
lean_dec(v___x_3296_);
return v_res_3308_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t v___x_3309_, lean_object* v_x_3310_){
_start:
{
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object* v___x_3311_, lean_object* v_x_3312_){
_start:
{
uint8_t v___x_17430__boxed_3313_; uint8_t v_res_3314_; lean_object* v_r_3315_; 
v___x_17430__boxed_3313_ = lean_unbox(v___x_3311_);
v_res_3314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_17430__boxed_3313_, v_x_3312_);
lean_dec(v_x_3312_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object* v___x_3319_, lean_object* v_a_3320_, lean_object* v_numIndices_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v_params_3326_, lean_object* v___x_3327_, lean_object* v_a_3328_, lean_object* v___x_3329_, lean_object* v___x_3330_, lean_object* v___x_3331_, lean_object* v_args_3332_, lean_object* v_goalType_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v___x_3339_; uint8_t v___x_3340_; 
v___x_3339_ = lean_array_get_size(v_args_3332_);
v___x_3340_ = lean_nat_dec_eq(v___x_3339_, v___x_3319_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_dec_ref(v_goalType_3333_);
lean_dec_ref(v_args_3332_);
lean_dec(v___x_3330_);
lean_dec(v___x_3329_);
lean_dec_ref(v_a_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v_params_3326_);
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3324_);
lean_dec(v___x_3322_);
lean_dec(v_numIndices_3321_);
lean_dec(v___x_3319_);
v___x_3341_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3342_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3341_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3342_;
}
else
{
if (lean_obj_tag(v_a_3320_) == 7)
{
lean_object* v_binderType_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v_binderType_3343_ = lean_ctor_get(v_a_3320_, 1);
lean_inc_ref(v_binderType_3343_);
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v_binderType_3343_);
v___x_3345_ = 0;
v___x_3346_ = lean_box(0);
v___x_3347_ = l_Lean_Meta_mkFreshExprMVar(v___x_3344_, v___x_3345_, v___x_3346_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; uint8_t v___x_3352_; lean_object* v___x_3353_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
v___x_3349_ = l_Lean_Expr_mvarId_x21(v_a_3348_);
v___x_3350_ = lean_nat_add(v_numIndices_3321_, v___x_3319_);
v___x_3351_ = lean_box(0);
v___x_3352_ = 0;
v___x_3353_ = l_Lean_Meta_introNCore(v___x_3349_, v___x_3350_, v___x_3351_, v___x_3352_, v___x_3352_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v_fst_3355_; lean_object* v_snd_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v_fst_3355_ = lean_ctor_get(v_a_3354_, 0);
lean_inc(v_fst_3355_);
v_snd_3356_ = lean_ctor_get(v_a_3354_, 1);
lean_inc_n(v_snd_3356_, 2);
lean_dec(v_a_3354_);
v___f_3357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0));
v___x_3358_ = lean_array_fget(v_args_3332_, v___x_3322_);
v___x_3359_ = lean_array_get_size(v_fst_3355_);
v___x_3360_ = lean_nat_sub(v___x_3359_, v___x_3319_);
v___x_3361_ = lean_array_get(v___x_3323_, v_fst_3355_, v___x_3360_);
v___x_3362_ = lean_box(v___x_3340_);
v___x_3363_ = lean_box(v___x_3352_);
v___x_3364_ = lean_box(v___x_3345_);
v___f_3365_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed), 31, 26);
lean_closure_set(v___f_3365_, 0, v___x_3361_);
lean_closure_set(v___f_3365_, 1, v___x_3362_);
lean_closure_set(v___f_3365_, 2, v_snd_3356_);
lean_closure_set(v___f_3365_, 3, v___x_3324_);
lean_closure_set(v___f_3365_, 4, v___x_3363_);
lean_closure_set(v___f_3365_, 5, v___x_3358_);
lean_closure_set(v___f_3365_, 6, v___x_3325_);
lean_closure_set(v___f_3365_, 7, v_a_3348_);
lean_closure_set(v___f_3365_, 8, v___x_3319_);
lean_closure_set(v___f_3365_, 9, v___x_3364_);
lean_closure_set(v___f_3365_, 10, v___x_3346_);
lean_closure_set(v___f_3365_, 11, v___x_3322_);
lean_closure_set(v___f_3365_, 12, v_params_3326_);
lean_closure_set(v___f_3365_, 13, v_args_3332_);
lean_closure_set(v___f_3365_, 14, v___x_3327_);
lean_closure_set(v___f_3365_, 15, v_a_3328_);
lean_closure_set(v___f_3365_, 16, v___x_3329_);
lean_closure_set(v___f_3365_, 17, v___f_3357_);
lean_closure_set(v___f_3365_, 18, v___x_3351_);
lean_closure_set(v___f_3365_, 19, v___x_3330_);
lean_closure_set(v___f_3365_, 20, v_numIndices_3321_);
lean_closure_set(v___f_3365_, 21, v_goalType_3333_);
lean_closure_set(v___f_3365_, 22, v___x_3360_);
lean_closure_set(v___f_3365_, 23, v___x_3359_);
lean_closure_set(v___f_3365_, 24, v_fst_3355_);
lean_closure_set(v___f_3365_, 25, v___x_3331_);
v___x_3366_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3356_, v___f_3365_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3366_;
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec(v_a_3348_);
lean_dec_ref(v_goalType_3333_);
lean_dec_ref(v_args_3332_);
lean_dec(v___x_3330_);
lean_dec(v___x_3329_);
lean_dec_ref(v_a_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v_params_3326_);
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3324_);
lean_dec(v___x_3322_);
lean_dec(v_numIndices_3321_);
lean_dec(v___x_3319_);
v_a_3367_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3353_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3353_);
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
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v_goalType_3333_);
lean_dec_ref(v_args_3332_);
lean_dec(v___x_3330_);
lean_dec(v___x_3329_);
lean_dec_ref(v_a_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v_params_3326_);
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3324_);
lean_dec(v___x_3322_);
lean_dec(v_numIndices_3321_);
lean_dec(v___x_3319_);
v_a_3375_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3347_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3347_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref(v_goalType_3333_);
lean_dec_ref(v_args_3332_);
lean_dec(v___x_3330_);
lean_dec(v___x_3329_);
lean_dec_ref(v_a_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v_params_3326_);
lean_dec_ref(v___x_3325_);
lean_dec_ref(v___x_3324_);
lean_dec(v___x_3322_);
lean_dec(v_numIndices_3321_);
lean_dec(v___x_3319_);
v___x_3383_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3384_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3383_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
return v___x_3384_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object** _args){
lean_object* v___x_3385_ = _args[0];
lean_object* v_a_3386_ = _args[1];
lean_object* v_numIndices_3387_ = _args[2];
lean_object* v___x_3388_ = _args[3];
lean_object* v___x_3389_ = _args[4];
lean_object* v___x_3390_ = _args[5];
lean_object* v___x_3391_ = _args[6];
lean_object* v_params_3392_ = _args[7];
lean_object* v___x_3393_ = _args[8];
lean_object* v_a_3394_ = _args[9];
lean_object* v___x_3395_ = _args[10];
lean_object* v___x_3396_ = _args[11];
lean_object* v___x_3397_ = _args[12];
lean_object* v_args_3398_ = _args[13];
lean_object* v_goalType_3399_ = _args[14];
lean_object* v___y_3400_ = _args[15];
lean_object* v___y_3401_ = _args[16];
lean_object* v___y_3402_ = _args[17];
lean_object* v___y_3403_ = _args[18];
lean_object* v___y_3404_ = _args[19];
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3385_, v_a_3386_, v_numIndices_3387_, v___x_3388_, v___x_3389_, v___x_3390_, v___x_3391_, v_params_3392_, v___x_3393_, v_a_3394_, v___x_3395_, v___x_3396_, v___x_3397_, v_args_3398_, v_goalType_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___x_3389_);
lean_dec_ref(v_a_3386_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___x_3412_; lean_object* v_env_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; 
v___x_3412_ = lean_st_ref_get(v___y_3410_);
v_env_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc_ref(v_env_3413_);
lean_dec(v___x_3412_);
v___x_3414_ = 0;
lean_inc(v_constName_3406_);
v___x_3415_ = l_Lean_Environment_findConstVal_x3f(v_env_3413_, v_constName_3406_, v___x_3414_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_);
return v___x_3416_;
}
else
{
lean_object* v_val_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec(v_constName_3406_);
v_val_3417_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3415_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_val_3417_);
lean_dec(v___x_3415_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 0);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_val_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___x_3438_; 
lean_inc(v_constName_3432_);
v___x_3438_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3450_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3450_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3450_ == 0)
{
v___x_3441_ = v___x_3438_;
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3450_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v_levelParams_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3448_; 
v_levelParams_3443_ = lean_ctor_get(v_a_3439_, 1);
lean_inc(v_levelParams_3443_);
lean_dec(v_a_3439_);
v___x_3444_ = lean_box(0);
v___x_3445_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3443_, v___x_3444_);
v___x_3446_ = l_Lean_mkConst(v_constName_3432_, v___x_3445_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3446_);
v___x_3448_ = v___x_3441_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec(v_constName_3432_);
v_a_3451_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3438_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3438_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3459_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec(v___y_3461_);
lean_dec_ref(v___y_3460_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v_levels_3468_, lean_object* v_params_3469_, lean_object* v___y_3470_, lean_object* v_predicates_3471_, lean_object* v_as_3472_, size_t v_sz_3473_, size_t v_i_3474_, lean_object* v_b_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
uint8_t v___x_3481_; 
v___x_3481_ = lean_usize_dec_lt(v_i_3474_, v_sz_3473_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; 
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_params_3469_);
lean_dec(v_levels_3468_);
v___x_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3482_, 0, v_b_3475_);
return v___x_3482_;
}
else
{
lean_object* v_a_3483_; lean_object* v_toConstantVal_3484_; lean_object* v_numParams_3485_; lean_object* v_numIndices_3486_; lean_object* v_name_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; 
v_a_3483_ = lean_array_uget_borrowed(v_as_3472_, v_i_3474_);
v_toConstantVal_3484_ = lean_ctor_get(v_a_3483_, 0);
v_numParams_3485_ = lean_ctor_get(v_a_3483_, 1);
v_numIndices_3486_ = lean_ctor_get(v_a_3483_, 2);
v_name_3487_ = lean_ctor_get(v_toConstantVal_3484_, 0);
lean_inc(v_name_3487_);
v___x_3488_ = l_Lean_mkCasesOnName(v_name_3487_);
lean_inc(v___x_3488_);
v___x_3489_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3488_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3491_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc(v_a_3490_);
lean_dec_ref_known(v___x_3489_, 1);
v___x_3491_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3488_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
lean_inc_ref(v_params_3469_);
v___x_3493_ = l_Array_append___redArg(v_params_3469_, v_predicates_3471_);
v___x_3494_ = l_Lean_mkAppN(v_a_3492_, v___x_3493_);
lean_dec_ref(v___x_3493_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc_ref(v___x_3494_);
v___x_3495_ = lean_infer_type(v___x_3494_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc_ref(v___x_3494_);
v___x_3497_ = lean_infer_type(v___x_3494_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___f_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___f_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = lean_unsigned_to_nat(0u);
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_box(0);
lean_inc_ref(v___y_3470_);
lean_inc_ref_n(v_params_3469_, 2);
lean_inc_n(v_levels_3468_, 2);
lean_inc_n(v_name_3487_, 2);
lean_inc(v_numParams_3485_);
v___f_3502_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3502_, 0, v_numParams_3485_);
lean_closure_set(v___f_3502_, 1, v_name_3487_);
lean_closure_set(v___f_3502_, 2, v_levels_3468_);
lean_closure_set(v___f_3502_, 3, v_params_3469_);
lean_closure_set(v___f_3502_, 4, v___y_3470_);
lean_closure_set(v___f_3502_, 5, v___x_3499_);
v___x_3503_ = lean_replace_expr(v___f_3502_, v_a_3496_);
lean_dec(v_a_3496_);
lean_dec_ref(v___f_3502_);
v___x_3504_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3487_);
v___x_3505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3504_);
v___x_3506_ = l_Lean_Name_append(v___x_3504_, v___x_3505_);
v___x_3507_ = l_Lean_mkConst(v___x_3506_, v_levels_3468_);
v___x_3508_ = lean_unsigned_to_nat(1u);
v___x_3509_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3503_);
lean_inc(v_numIndices_3486_);
v___f_3510_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed), 20, 13);
lean_closure_set(v___f_3510_, 0, v___x_3508_);
lean_closure_set(v___f_3510_, 1, v_a_3498_);
lean_closure_set(v___f_3510_, 2, v_numIndices_3486_);
lean_closure_set(v___f_3510_, 3, v___x_3499_);
lean_closure_set(v___f_3510_, 4, v___x_3500_);
lean_closure_set(v___f_3510_, 5, v___x_3507_);
lean_closure_set(v___f_3510_, 6, v___x_3494_);
lean_closure_set(v___f_3510_, 7, v_params_3469_);
lean_closure_set(v___f_3510_, 8, v___x_3503_);
lean_closure_set(v___f_3510_, 9, v_a_3490_);
lean_closure_set(v___f_3510_, 10, v___x_3504_);
lean_closure_set(v___f_3510_, 11, v___x_3509_);
lean_closure_set(v___f_3510_, 12, v___x_3501_);
v___x_3511_ = 0;
v___x_3512_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_3503_, v___x_3509_, v___f_3510_, v___x_3511_, v___x_3511_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
if (lean_obj_tag(v___x_3512_) == 0)
{
size_t v___x_3513_; size_t v___x_3514_; 
lean_dec_ref_known(v___x_3512_, 1);
v___x_3513_ = ((size_t)1ULL);
v___x_3514_ = lean_usize_add(v_i_3474_, v___x_3513_);
v_i_3474_ = v___x_3514_;
v_b_3475_ = v___x_3501_;
goto _start;
}
else
{
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_params_3469_);
lean_dec(v_levels_3468_);
return v___x_3512_;
}
}
else
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3523_; 
lean_dec(v_a_3496_);
lean_dec_ref(v___x_3494_);
lean_dec(v_a_3490_);
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_params_3469_);
lean_dec(v_levels_3468_);
v_a_3516_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3523_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3523_ == 0)
{
v___x_3518_ = v___x_3497_;
v_isShared_3519_ = v_isSharedCheck_3523_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3497_);
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
lean_dec_ref(v___x_3494_);
lean_dec(v_a_3490_);
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_params_3469_);
lean_dec(v_levels_3468_);
v_a_3524_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3495_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3495_);
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
lean_dec(v_a_3490_);
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_params_3469_);
lean_dec(v_levels_3468_);
v_a_3532_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3491_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3491_);
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
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v___x_3488_);
lean_dec_ref(v___y_3470_);
lean_dec_ref(v_params_3469_);
lean_dec(v_levels_3468_);
v_a_3540_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3489_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3489_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v_levels_3548_, lean_object* v_params_3549_, lean_object* v___y_3550_, lean_object* v_predicates_3551_, lean_object* v_as_3552_, lean_object* v_sz_3553_, lean_object* v_i_3554_, lean_object* v_b_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
size_t v_sz_boxed_3561_; size_t v_i_boxed_3562_; lean_object* v_res_3563_; 
v_sz_boxed_3561_ = lean_unbox_usize(v_sz_3553_);
lean_dec(v_sz_3553_);
v_i_boxed_3562_ = lean_unbox_usize(v_i_3554_);
lean_dec(v_i_3554_);
v_res_3563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3548_, v_params_3549_, v___y_3550_, v_predicates_3551_, v_as_3552_, v_sz_boxed_3561_, v_i_boxed_3562_, v_b_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v_as_3552_);
lean_dec_ref(v_predicates_3551_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3564_, size_t v_sz_3565_, size_t v_i_3566_, lean_object* v_bs_3567_){
_start:
{
uint8_t v___x_3568_; 
v___x_3568_ = lean_usize_dec_lt(v_i_3566_, v_sz_3565_);
if (v___x_3568_ == 0)
{
lean_dec(v_levels_3564_);
return v_bs_3567_;
}
else
{
lean_object* v_v_3569_; lean_object* v_toConstantVal_3570_; lean_object* v_name_3571_; lean_object* v___x_3572_; lean_object* v_bs_x27_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; size_t v___x_3576_; size_t v___x_3577_; lean_object* v___x_3578_; 
v_v_3569_ = lean_array_uget_borrowed(v_bs_3567_, v_i_3566_);
v_toConstantVal_3570_ = lean_ctor_get(v_v_3569_, 0);
v_name_3571_ = lean_ctor_get(v_toConstantVal_3570_, 0);
lean_inc(v_name_3571_);
v___x_3572_ = lean_unsigned_to_nat(0u);
v_bs_x27_3573_ = lean_array_uset(v_bs_3567_, v_i_3566_, v___x_3572_);
v___x_3574_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3571_);
lean_inc(v_levels_3564_);
v___x_3575_ = l_Lean_mkConst(v___x_3574_, v_levels_3564_);
v___x_3576_ = ((size_t)1ULL);
v___x_3577_ = lean_usize_add(v_i_3566_, v___x_3576_);
v___x_3578_ = lean_array_uset(v_bs_x27_3573_, v_i_3566_, v___x_3575_);
v_i_3566_ = v___x_3577_;
v_bs_3567_ = v___x_3578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3580_, lean_object* v_sz_3581_, lean_object* v_i_3582_, lean_object* v_bs_3583_){
_start:
{
size_t v_sz_boxed_3584_; size_t v_i_boxed_3585_; lean_object* v_res_3586_; 
v_sz_boxed_3584_ = lean_unbox_usize(v_sz_3581_);
lean_dec(v_sz_3581_);
v_i_boxed_3585_ = lean_unbox_usize(v_i_3582_);
lean_dec(v_i_3582_);
v_res_3586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3580_, v_sz_boxed_3584_, v_i_boxed_3585_, v_bs_3583_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3587_, lean_object* v_levels_3588_, lean_object* v___y_3589_, lean_object* v_params_3590_, lean_object* v_x_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
size_t v_sz_3597_; size_t v___x_3598_; lean_object* v_predicates_3599_; size_t v_sz_3600_; lean_object* v_predicates_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_sz_3597_ = lean_array_size(v_infos_3587_);
v___x_3598_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3587_);
lean_inc(v_levels_3588_);
v_predicates_3599_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3588_, v_sz_3597_, v___x_3598_, v_infos_3587_);
v_sz_3600_ = lean_array_size(v_predicates_3599_);
v_predicates_3601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3590_, v_sz_3600_, v___x_3598_, v_predicates_3599_);
v___x_3602_ = lean_box(0);
v___x_3603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3588_, v_params_3590_, v___y_3589_, v_predicates_3601_, v_infos_3587_, v_sz_3597_, v___x_3598_, v___x_3602_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
lean_dec_ref(v_infos_3587_);
lean_dec_ref(v_predicates_3601_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v___x_3603_, 0);
lean_dec(v_unused_3611_);
v___x_3605_ = v___x_3603_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_dec(v___x_3603_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 0, v___x_3602_);
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3602_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
return v___x_3603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3612_, lean_object* v_levels_3613_, lean_object* v___y_3614_, lean_object* v_params_3615_, lean_object* v_x_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3612_, v_levels_3613_, v___y_3614_, v_params_3615_, v_x_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec_ref(v_x_3616_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3623_, size_t v_i_3624_, size_t v_stop_3625_, lean_object* v_b_3626_){
_start:
{
uint8_t v___x_3627_; 
v___x_3627_ = lean_usize_dec_eq(v_i_3624_, v_stop_3625_);
if (v___x_3627_ == 0)
{
lean_object* v___x_3628_; lean_object* v_ctors_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; size_t v___x_3632_; size_t v___x_3633_; 
v___x_3628_ = lean_array_uget_borrowed(v_as_3623_, v_i_3624_);
v_ctors_3629_ = lean_ctor_get(v___x_3628_, 4);
lean_inc(v_ctors_3629_);
v___x_3630_ = lean_array_mk(v_ctors_3629_);
v___x_3631_ = l_Array_append___redArg(v_b_3626_, v___x_3630_);
lean_dec_ref(v___x_3630_);
v___x_3632_ = ((size_t)1ULL);
v___x_3633_ = lean_usize_add(v_i_3624_, v___x_3632_);
v_i_3624_ = v___x_3633_;
v_b_3626_ = v___x_3631_;
goto _start;
}
else
{
return v_b_3626_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_stop_3637_, lean_object* v_b_3638_){
_start:
{
size_t v_i_boxed_3639_; size_t v_stop_boxed_3640_; lean_object* v_res_3641_; 
v_i_boxed_3639_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_stop_boxed_3640_ = lean_unbox_usize(v_stop_3637_);
lean_dec(v_stop_3637_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3635_, v_i_boxed_3639_, v_stop_boxed_3640_, v_b_3638_);
lean_dec_ref(v_as_3635_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v_toConstantVal_3653_; lean_object* v_numParams_3654_; lean_object* v_levelParams_3655_; lean_object* v_type_3656_; lean_object* v___x_3657_; lean_object* v_levels_3658_; lean_object* v___y_3660_; lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3650_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3651_ = lean_unsigned_to_nat(0u);
v___x_3652_ = lean_array_get_borrowed(v___x_3650_, v_infos_3644_, v___x_3651_);
v_toConstantVal_3653_ = lean_ctor_get(v___x_3652_, 0);
v_numParams_3654_ = lean_ctor_get(v___x_3652_, 1);
lean_inc(v_numParams_3654_);
v_levelParams_3655_ = lean_ctor_get(v_toConstantVal_3653_, 1);
v_type_3656_ = lean_ctor_get(v_toConstantVal_3653_, 2);
lean_inc_ref(v_type_3656_);
v___x_3657_ = lean_box(0);
lean_inc(v_levelParams_3655_);
v_levels_3658_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3655_, v___x_3657_);
v___x_3667_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3668_ = lean_array_get_size(v_infos_3644_);
v___x_3669_ = lean_nat_dec_lt(v___x_3651_, v___x_3668_);
if (v___x_3669_ == 0)
{
v___y_3660_ = v___x_3667_;
goto v___jp_3659_;
}
else
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_nat_dec_le(v___x_3668_, v___x_3668_);
if (v___x_3670_ == 0)
{
if (v___x_3669_ == 0)
{
v___y_3660_ = v___x_3667_;
goto v___jp_3659_;
}
else
{
size_t v___x_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v___x_3671_ = ((size_t)0ULL);
v___x_3672_ = lean_usize_of_nat(v___x_3668_);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3644_, v___x_3671_, v___x_3672_, v___x_3667_);
v___y_3660_ = v___x_3673_;
goto v___jp_3659_;
}
}
else
{
size_t v___x_3674_; size_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = ((size_t)0ULL);
v___x_3675_ = lean_usize_of_nat(v___x_3668_);
v___x_3676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3644_, v___x_3674_, v___x_3675_, v___x_3667_);
v___y_3660_ = v___x_3676_;
goto v___jp_3659_;
}
}
v___jp_3659_:
{
lean_object* v___f_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; uint8_t v___x_3665_; lean_object* v___x_3666_; 
lean_inc_ref(v_infos_3644_);
v___f_3661_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3661_, 0, v_infos_3644_);
lean_closure_set(v___f_3661_, 1, v_levels_3658_);
lean_closure_set(v___f_3661_, 2, v___y_3660_);
v___x_3662_ = lean_array_get_size(v_infos_3644_);
lean_dec_ref(v_infos_3644_);
v___x_3663_ = lean_nat_sub(v_numParams_3654_, v___x_3662_);
lean_dec(v_numParams_3654_);
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
v___x_3665_ = 0;
v___x_3666_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_3656_, v___x_3664_, v___f_3661_, v___x_3665_, v___x_3665_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
return v___x_3666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3684_, lean_object* v_constName_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
return v___x_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3692_, lean_object* v_constName_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3692_, v_constName_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___y_3697_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3700_, lean_object* v_ref_3701_, lean_object* v_constName_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; 
v___x_3708_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3701_, v_constName_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3709_, lean_object* v_ref_3710_, lean_object* v_constName_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3709_, v_ref_3710_, v_constName_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v_ref_3710_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3718_, lean_object* v_ref_3719_, lean_object* v_msg_3720_, lean_object* v_declHint_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v___x_3727_; 
v___x_3727_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3719_, v_msg_3720_, v_declHint_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3728_, lean_object* v_ref_3729_, lean_object* v_msg_3730_, lean_object* v_declHint_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3728_, v_ref_3729_, v_msg_3730_, v_declHint_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
lean_dec(v_ref_3729_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3738_, lean_object* v_declHint_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3738_, v_declHint_3739_, v___y_3743_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3746_, lean_object* v_declHint_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v_res_3753_; 
v_res_3753_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3746_, v_declHint_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
lean_dec(v___y_3749_);
lean_dec_ref(v___y_3748_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3754_, lean_object* v_ref_3755_, lean_object* v_msg_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; 
v___x_3762_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3755_, v_msg_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3763_, lean_object* v_ref_3764_, lean_object* v_msg_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v_res_3771_; 
v_res_3771_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3763_, v_ref_3764_, v_msg_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v_ref_3764_);
return v_res_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3775_, lean_object* v___x_3776_, lean_object* v_params_3777_, size_t v_sz_3778_, size_t v_i_3779_, lean_object* v_bs_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
uint8_t v___x_3786_; 
v___x_3786_ = lean_usize_dec_lt(v_i_3779_, v_sz_3778_);
if (v___x_3786_ == 0)
{
lean_object* v___x_3787_; 
lean_dec_ref(v_params_3777_);
lean_dec_ref(v___x_3776_);
lean_dec(v___x_3775_);
v___x_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3787_, 0, v_bs_3780_);
return v___x_3787_;
}
else
{
lean_object* v_v_3788_; lean_object* v_toConstantVal_3789_; lean_object* v_name_3790_; lean_object* v___x_3791_; lean_object* v_bs_x27_3792_; lean_object* v___y_3794_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
v_v_3788_ = lean_array_uget_borrowed(v_bs_3780_, v_i_3779_);
v_toConstantVal_3789_ = lean_ctor_get(v_v_3788_, 0);
v_name_3790_ = lean_ctor_get(v_toConstantVal_3789_, 0);
lean_inc(v_name_3790_);
v___x_3791_ = lean_unsigned_to_nat(0u);
v_bs_x27_3792_ = lean_array_uset(v_bs_3780_, v_i_3779_, v___x_3791_);
v___x_3808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3809_ = l_Lean_Name_append(v_name_3790_, v___x_3808_);
lean_inc(v___x_3775_);
v___x_3810_ = l_Lean_mkConst(v___x_3809_, v___x_3775_);
v___x_3811_ = l_Lean_Meta_unfoldDefinition(v___x_3810_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; size_t v_sz_3813_; size_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_a_3812_);
lean_dec_ref_known(v___x_3811_, 1);
v_sz_3813_ = lean_array_size(v___x_3776_);
v___x_3814_ = ((size_t)0ULL);
lean_inc_ref(v___x_3776_);
v___x_3815_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3777_, v_sz_3813_, v___x_3814_, v___x_3776_);
lean_inc_ref(v_params_3777_);
v___x_3816_ = l_Array_append___redArg(v_params_3777_, v___x_3815_);
lean_dec_ref(v___x_3815_);
v___x_3817_ = l_Lean_mkAppN(v_a_3812_, v___x_3816_);
lean_dec_ref(v___x_3816_);
v___x_3818_ = 0;
v___x_3819_ = 1;
v___x_3820_ = l_Lean_Meta_mkLambdaFVars(v_params_3777_, v___x_3817_, v___x_3818_, v___x_3786_, v___x_3818_, v___x_3786_, v___x_3819_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
v___y_3794_ = v___x_3820_;
goto v___jp_3793_;
}
else
{
v___y_3794_ = v___x_3811_;
goto v___jp_3793_;
}
v___jp_3793_:
{
if (lean_obj_tag(v___y_3794_) == 0)
{
lean_object* v_a_3795_; size_t v___x_3796_; size_t v___x_3797_; lean_object* v___x_3798_; 
v_a_3795_ = lean_ctor_get(v___y_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___y_3794_, 1);
v___x_3796_ = ((size_t)1ULL);
v___x_3797_ = lean_usize_add(v_i_3779_, v___x_3796_);
v___x_3798_ = lean_array_uset(v_bs_x27_3792_, v_i_3779_, v_a_3795_);
v_i_3779_ = v___x_3797_;
v_bs_3780_ = v___x_3798_;
goto _start;
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v_bs_x27_3792_);
lean_dec_ref(v_params_3777_);
lean_dec_ref(v___x_3776_);
lean_dec(v___x_3775_);
v_a_3800_ = lean_ctor_get(v___y_3794_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___y_3794_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___y_3794_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___y_3794_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3821_, lean_object* v___x_3822_, lean_object* v_params_3823_, lean_object* v_sz_3824_, lean_object* v_i_3825_, lean_object* v_bs_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
size_t v_sz_boxed_3832_; size_t v_i_boxed_3833_; lean_object* v_res_3834_; 
v_sz_boxed_3832_ = lean_unbox_usize(v_sz_3824_);
lean_dec(v_sz_3824_);
v_i_boxed_3833_ = lean_unbox_usize(v_i_3825_);
lean_dec(v_i_3825_);
v_res_3834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3821_, v___x_3822_, v_params_3823_, v_sz_boxed_3832_, v_i_boxed_3833_, v_bs_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec_ref(v___y_3827_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3835_, lean_object* v___x_3836_, size_t v_sz_3837_, size_t v___x_3838_, lean_object* v_a_3839_, lean_object* v_params_3840_, lean_object* v_x_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3835_, v___x_3836_, v_params_3840_, v_sz_3837_, v___x_3838_, v_a_3839_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3850_, lean_object* v___x_3851_, lean_object* v_sz_3852_, lean_object* v___x_3853_, lean_object* v_a_3854_, lean_object* v_params_3855_, lean_object* v_x_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
size_t v_sz_boxed_3864_; size_t v___x_5221__boxed_3865_; lean_object* v_res_3866_; 
v_sz_boxed_3864_ = lean_unbox_usize(v_sz_3852_);
lean_dec(v_sz_3852_);
v___x_5221__boxed_3865_ = lean_unbox_usize(v___x_3853_);
lean_dec(v___x_3853_);
v_res_3866_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3850_, v___x_3851_, v_sz_boxed_3864_, v___x_5221__boxed_3865_, v_a_3854_, v_params_3855_, v_x_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec(v___y_3858_);
lean_dec_ref(v___y_3857_);
lean_dec_ref(v_x_3856_);
return v_res_3866_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0));
v___x_3869_ = l_Lean_stringToMessageData(v___x_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object* v_constName_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v___x_3878_; lean_object* v_env_3879_; lean_object* v___x_3880_; 
v___x_3878_ = lean_st_ref_get(v___y_3876_);
v_env_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc_ref(v_env_3879_);
lean_dec(v___x_3878_);
lean_inc(v_constName_3870_);
v___x_3880_ = l_Lean_isInductiveCore_x3f(v_env_3879_, v_constName_3870_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v___x_3881_; uint8_t v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3881_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_3882_ = 0;
v___x_3883_ = l_Lean_MessageData_ofConstName(v_constName_3870_, v___x_3882_);
v___x_3884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3881_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_3886_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
return v___x_3887_;
}
else
{
lean_object* v_val_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_constName_3870_);
v_val_3888_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3880_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_val_3888_);
lean_dec(v___x_3880_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
lean_ctor_set_tag(v___x_3890_, 0);
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_val_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object* v_constName_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t v_sz_3905_, size_t v_i_3906_, lean_object* v_bs_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
uint8_t v___x_3915_; 
v___x_3915_ = lean_usize_dec_lt(v_i_3906_, v_sz_3905_);
if (v___x_3915_ == 0)
{
lean_object* v___x_3916_; 
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v_bs_3907_);
return v___x_3916_;
}
else
{
lean_object* v_v_3917_; lean_object* v_declName_3918_; lean_object* v___x_3919_; 
v_v_3917_ = lean_array_uget_borrowed(v_bs_3907_, v_i_3906_);
v_declName_3918_ = lean_ctor_get(v_v_3917_, 1);
lean_inc(v_declName_3918_);
v___x_3919_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_3918_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3921_; lean_object* v_bs_x27_3922_; size_t v___x_3923_; size_t v___x_3924_; lean_object* v___x_3925_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___x_3921_ = lean_unsigned_to_nat(0u);
v_bs_x27_3922_ = lean_array_uset(v_bs_3907_, v_i_3906_, v___x_3921_);
v___x_3923_ = ((size_t)1ULL);
v___x_3924_ = lean_usize_add(v_i_3906_, v___x_3923_);
v___x_3925_ = lean_array_uset(v_bs_x27_3922_, v_i_3906_, v_a_3920_);
v_i_3906_ = v___x_3924_;
v_bs_3907_ = v___x_3925_;
goto _start;
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v_bs_3907_);
v_a_3927_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3919_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3919_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object* v_sz_3935_, lean_object* v_i_3936_, lean_object* v_bs_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3935_);
lean_dec(v_sz_3935_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3936_);
lean_dec(v_i_3936_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_3945_, v_i_boxed_3946_, v_bs_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
return v_res_3947_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; 
v___x_3948_ = l_Lean_instInhabitedExpr;
v___x_3949_ = lean_box(0);
v___x_3950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3950_, 0, v___x_3949_);
lean_ctor_set(v___x_3950_, 1, v___x_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3951_, lean_object* v_a_3952_, lean_object* v___x_3953_, lean_object* v_as_3954_, lean_object* v_i_3955_, lean_object* v_j_3956_, lean_object* v_bs_3957_){
_start:
{
lean_object* v_zero_3958_; uint8_t v_isZero_3959_; 
v_zero_3958_ = lean_unsigned_to_nat(0u);
v_isZero_3959_ = lean_nat_dec_eq(v_i_3955_, v_zero_3958_);
if (v_isZero_3959_ == 1)
{
lean_dec(v_j_3956_);
lean_dec(v_i_3955_);
lean_dec(v___x_3953_);
return v_bs_3957_;
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v_ref_3962_; lean_object* v_modifiers_3963_; uint8_t v_isGreatest_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v_fst_3967_; lean_object* v_snd_3968_; lean_object* v_one_3969_; lean_object* v_n_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; uint8_t v___y_3975_; 
v___x_3960_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v___x_3961_ = lean_array_get_borrowed(v___x_3960_, v_coinductiveElabData_3951_, v_j_3956_);
v_ref_3962_ = lean_ctor_get(v___x_3961_, 2);
v_modifiers_3963_ = lean_ctor_get(v___x_3961_, 3);
v_isGreatest_3964_ = lean_ctor_get_uint8(v___x_3961_, sizeof(void*)*5);
v___x_3965_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3966_ = lean_array_get_borrowed(v___x_3965_, v_a_3952_, v_j_3956_);
v_fst_3967_ = lean_ctor_get(v___x_3966_, 0);
v_snd_3968_ = lean_ctor_get(v___x_3966_, 1);
v_one_3969_ = lean_unsigned_to_nat(1u);
v_n_3970_ = lean_nat_sub(v_i_3955_, v_one_3969_);
lean_dec(v_i_3955_);
v___x_3971_ = lean_array_fget_borrowed(v_as_3954_, v_j_3956_);
v___x_3972_ = 0;
v___x_3973_ = lean_box(0);
if (v_isGreatest_3964_ == 0)
{
uint8_t v___x_3983_; 
v___x_3983_ = 2;
v___y_3975_ = v___x_3983_;
goto v___jp_3974_;
}
else
{
uint8_t v___x_3984_; 
v___x_3984_ = 1;
v___y_3975_ = v___x_3984_;
goto v___jp_3974_;
}
v___jp_3974_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
lean_inc_n(v_ref_3962_, 4);
v___x_3976_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3976_, 0, v_ref_3962_);
lean_ctor_set(v___x_3976_, 1, v___x_3973_);
lean_ctor_set_uint8(v___x_3976_, sizeof(void*)*2, v___y_3975_);
v___x_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
v___x_3978_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3978_, 0, v_ref_3962_);
lean_ctor_set(v___x_3978_, 1, v___x_3973_);
lean_ctor_set(v___x_3978_, 2, v___x_3973_);
lean_ctor_set(v___x_3978_, 3, v___x_3977_);
lean_ctor_set(v___x_3978_, 4, v___x_3973_);
lean_ctor_set(v___x_3978_, 5, v_zero_3958_);
lean_inc(v___x_3971_);
lean_inc(v_snd_3968_);
lean_inc(v_fst_3967_);
lean_inc_ref(v_modifiers_3963_);
lean_inc(v___x_3953_);
v___x_3979_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3979_, 0, v_ref_3962_);
lean_ctor_set(v___x_3979_, 1, v___x_3953_);
lean_ctor_set(v___x_3979_, 2, v_modifiers_3963_);
lean_ctor_set(v___x_3979_, 3, v_fst_3967_);
lean_ctor_set(v___x_3979_, 4, v_ref_3962_);
lean_ctor_set(v___x_3979_, 5, v_zero_3958_);
lean_ctor_set(v___x_3979_, 6, v_snd_3968_);
lean_ctor_set(v___x_3979_, 7, v___x_3971_);
lean_ctor_set(v___x_3979_, 8, v___x_3978_);
lean_ctor_set_uint8(v___x_3979_, sizeof(void*)*9, v___x_3972_);
v___x_3980_ = lean_nat_add(v_j_3956_, v_one_3969_);
lean_dec(v_j_3956_);
v___x_3981_ = lean_array_push(v_bs_3957_, v___x_3979_);
v_i_3955_ = v_n_3970_;
v_j_3956_ = v___x_3980_;
v_bs_3957_ = v___x_3981_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object* v_coinductiveElabData_3985_, lean_object* v_a_3986_, lean_object* v___x_3987_, lean_object* v_as_3988_, lean_object* v_i_3989_, lean_object* v_j_3990_, lean_object* v_bs_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_3985_, v_a_3986_, v___x_3987_, v_as_3988_, v_i_3989_, v_j_3990_, v_bs_3991_);
lean_dec_ref(v_as_3988_);
lean_dec_ref(v_a_3986_);
lean_dec_ref(v_coinductiveElabData_3985_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
if (lean_obj_tag(v_a_3993_) == 0)
{
lean_object* v___x_3995_; 
v___x_3995_ = l_List_reverse___redArg(v_a_3994_);
return v___x_3995_;
}
else
{
lean_object* v_head_3996_; lean_object* v_tail_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4006_; 
v_head_3996_ = lean_ctor_get(v_a_3993_, 0);
v_tail_3997_ = lean_ctor_get(v_a_3993_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_a_3993_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3999_ = v_a_3993_;
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_tail_3997_);
lean_inc(v_head_3996_);
lean_dec(v_a_3993_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
v___x_4001_ = l_Lean_MessageData_ofName(v_head_3996_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 1, v_a_3994_);
lean_ctor_set(v___x_3999_, 0, v___x_4001_);
v___x_4003_ = v___x_3999_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_a_3994_);
v___x_4003_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
v_a_3993_ = v_tail_3997_;
v_a_3994_ = v___x_4003_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t v_sz_4007_, size_t v_i_4008_, lean_object* v_bs_4009_){
_start:
{
uint8_t v___x_4010_; 
v___x_4010_ = lean_usize_dec_lt(v_i_4008_, v_sz_4007_);
if (v___x_4010_ == 0)
{
return v_bs_4009_;
}
else
{
lean_object* v_v_4011_; lean_object* v_declName_4012_; lean_object* v___x_4013_; lean_object* v_bs_x27_4014_; size_t v___x_4015_; size_t v___x_4016_; lean_object* v___x_4017_; 
v_v_4011_ = lean_array_uget_borrowed(v_bs_4009_, v_i_4008_);
v_declName_4012_ = lean_ctor_get(v_v_4011_, 1);
lean_inc(v_declName_4012_);
v___x_4013_ = lean_unsigned_to_nat(0u);
v_bs_x27_4014_ = lean_array_uset(v_bs_4009_, v_i_4008_, v___x_4013_);
v___x_4015_ = ((size_t)1ULL);
v___x_4016_ = lean_usize_add(v_i_4008_, v___x_4015_);
v___x_4017_ = lean_array_uset(v_bs_x27_4014_, v_i_4008_, v_declName_4012_);
v_i_4008_ = v___x_4016_;
v_bs_4009_ = v___x_4017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object* v_sz_4019_, lean_object* v_i_4020_, lean_object* v_bs_4021_){
_start:
{
size_t v_sz_boxed_4022_; size_t v_i_boxed_4023_; lean_object* v_res_4024_; 
v_sz_boxed_4022_ = lean_unbox_usize(v_sz_4019_);
lean_dec(v_sz_4019_);
v_i_boxed_4023_ = lean_unbox_usize(v_i_4020_);
lean_dec(v_i_4020_);
v_res_4024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_4022_, v_i_boxed_4023_, v_bs_4021_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v_v_4025_, lean_object* v___x_4026_, lean_object* v___x_4027_, uint8_t v___x_4028_, lean_object* v_args_4029_, lean_object* v_body_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_numParams_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; uint8_t v___x_4046_; lean_object* v___x_4047_; 
v_numParams_4038_ = lean_ctor_get(v_v_4025_, 1);
lean_inc(v_numParams_4038_);
lean_dec(v_v_4025_);
lean_inc_ref(v_args_4029_);
v___x_4039_ = l_Array_toSubarray___redArg(v_args_4029_, v___x_4026_, v___x_4027_);
v___x_4040_ = l_Subarray_copy___redArg(v___x_4039_);
v___x_4041_ = lean_array_get_size(v_args_4029_);
v___x_4042_ = l_Array_toSubarray___redArg(v_args_4029_, v_numParams_4038_, v___x_4041_);
v___x_4043_ = l_Subarray_copy___redArg(v___x_4042_);
v___x_4044_ = l_Array_append___redArg(v___x_4040_, v___x_4043_);
lean_dec_ref(v___x_4043_);
v___x_4045_ = 0;
v___x_4046_ = 1;
v___x_4047_ = l_Lean_Meta_mkForallFVars(v___x_4044_, v_body_4030_, v___x_4045_, v___x_4028_, v___x_4028_, v___x_4046_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec_ref(v___x_4044_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v_v_4048_, lean_object* v___x_4049_, lean_object* v___x_4050_, lean_object* v___x_4051_, lean_object* v_args_4052_, lean_object* v_body_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
uint8_t v___x_5474__boxed_4061_; lean_object* v_res_4062_; 
v___x_5474__boxed_4061_ = lean_unbox(v___x_4051_);
v_res_4062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_4048_, v___x_4049_, v___x_4050_, v___x_5474__boxed_4061_, v_args_4052_, v_body_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_4063_, size_t v_sz_4064_, size_t v_i_4065_, lean_object* v_bs_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
uint8_t v___x_4074_; 
v___x_4074_ = lean_usize_dec_lt(v_i_4065_, v_sz_4064_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; 
lean_dec(v___x_4063_);
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_bs_4066_);
return v___x_4075_;
}
else
{
lean_object* v_v_4076_; lean_object* v_toConstantVal_4077_; lean_object* v_name_4078_; lean_object* v_type_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___f_4082_; uint8_t v___x_4083_; lean_object* v___x_4084_; 
v_v_4076_ = lean_array_uget_borrowed(v_bs_4066_, v_i_4065_);
v_toConstantVal_4077_ = lean_ctor_get(v_v_4076_, 0);
v_name_4078_ = lean_ctor_get(v_toConstantVal_4077_, 0);
lean_inc(v_name_4078_);
v_type_4079_ = lean_ctor_get(v_toConstantVal_4077_, 2);
v___x_4080_ = lean_unsigned_to_nat(0u);
v___x_4081_ = lean_box(v___x_4074_);
lean_inc(v___x_4063_);
lean_inc(v_v_4076_);
v___f_4082_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4082_, 0, v_v_4076_);
lean_closure_set(v___f_4082_, 1, v___x_4080_);
lean_closure_set(v___f_4082_, 2, v___x_4063_);
lean_closure_set(v___f_4082_, 3, v___x_4081_);
v___x_4083_ = 0;
lean_inc_ref(v_type_4079_);
v___x_4084_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4079_, v___f_4082_, v___x_4083_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v_bs_x27_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; size_t v___x_4089_; size_t v___x_4090_; lean_object* v___x_4091_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
v_bs_x27_4086_ = lean_array_uset(v_bs_4066_, v_i_4065_, v___x_4080_);
v___x_4087_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4078_);
v___x_4088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
lean_ctor_set(v___x_4088_, 1, v_a_4085_);
v___x_4089_ = ((size_t)1ULL);
v___x_4090_ = lean_usize_add(v_i_4065_, v___x_4089_);
v___x_4091_ = lean_array_uset(v_bs_x27_4086_, v_i_4065_, v___x_4088_);
v_i_4065_ = v___x_4090_;
v_bs_4066_ = v___x_4091_;
goto _start;
}
else
{
lean_object* v_a_4093_; lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4100_; 
lean_dec(v_name_4078_);
lean_dec_ref(v_bs_4066_);
lean_dec(v___x_4063_);
v_a_4093_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4095_ = v___x_4084_;
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
else
{
lean_inc(v_a_4093_);
lean_dec(v___x_4084_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4100_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4098_; 
if (v_isShared_4096_ == 0)
{
v___x_4098_ = v___x_4095_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4093_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object* v___x_4101_, lean_object* v_sz_4102_, lean_object* v_i_4103_, lean_object* v_bs_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
size_t v_sz_boxed_4112_; size_t v_i_boxed_4113_; lean_object* v_res_4114_; 
v_sz_boxed_4112_ = lean_unbox_usize(v_sz_4102_);
lean_dec(v_sz_4102_);
v_i_boxed_4113_ = lean_unbox_usize(v_i_4103_);
lean_dec(v_i_4103_);
v_res_4114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4101_, v_sz_boxed_4112_, v_i_boxed_4113_, v_bs_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object* v___x_4115_, size_t v_sz_4116_, size_t v_i_4117_, lean_object* v_bs_4118_){
_start:
{
uint8_t v___x_4119_; 
v___x_4119_ = lean_usize_dec_lt(v_i_4117_, v_sz_4116_);
if (v___x_4119_ == 0)
{
lean_dec(v___x_4115_);
return v_bs_4118_;
}
else
{
lean_object* v_v_4120_; lean_object* v_fst_4121_; lean_object* v___x_4122_; lean_object* v_bs_x27_4123_; lean_object* v___x_4124_; size_t v___x_4125_; size_t v___x_4126_; lean_object* v___x_4127_; 
v_v_4120_ = lean_array_uget_borrowed(v_bs_4118_, v_i_4117_);
v_fst_4121_ = lean_ctor_get(v_v_4120_, 0);
lean_inc(v_fst_4121_);
v___x_4122_ = lean_unsigned_to_nat(0u);
v_bs_x27_4123_ = lean_array_uset(v_bs_4118_, v_i_4117_, v___x_4122_);
lean_inc(v___x_4115_);
v___x_4124_ = l_Lean_mkConst(v_fst_4121_, v___x_4115_);
v___x_4125_ = ((size_t)1ULL);
v___x_4126_ = lean_usize_add(v_i_4117_, v___x_4125_);
v___x_4127_ = lean_array_uset(v_bs_x27_4123_, v_i_4117_, v___x_4124_);
v_i_4117_ = v___x_4126_;
v_bs_4118_ = v___x_4127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object* v___x_4129_, lean_object* v_sz_4130_, lean_object* v_i_4131_, lean_object* v_bs_4132_){
_start:
{
size_t v_sz_boxed_4133_; size_t v_i_boxed_4134_; lean_object* v_res_4135_; 
v_sz_boxed_4133_ = lean_unbox_usize(v_sz_4130_);
lean_dec(v_sz_4130_);
v_i_boxed_4134_ = lean_unbox_usize(v_i_4131_);
lean_dec(v_i_4131_);
v_res_4135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4129_, v_sz_boxed_4133_, v_i_boxed_4134_, v_bs_4132_);
return v_res_4135_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCoinductive___closed__1(void){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = ((lean_object*)(l_Lean_Elab_Command_elabCoinductive___closed__0));
v___x_4138_ = l_Lean_stringToMessageData(v___x_4137_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object* v_coinductiveElabData_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_options_4147_; lean_object* v_inheritedTraceOptions_4148_; uint8_t v_hasTrace_4149_; lean_object* v___x_4150_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; 
v_options_4147_ = lean_ctor_get(v_a_4144_, 2);
v_inheritedTraceOptions_4148_ = lean_ctor_get(v_a_4144_, 13);
v_hasTrace_4149_ = lean_ctor_get_uint8(v_options_4147_, sizeof(void*)*1);
v___x_4150_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4149_ == 0)
{
v___y_4152_ = v_a_4140_;
v___y_4153_ = v_a_4141_;
v___y_4154_ = v_a_4142_;
v___y_4155_ = v_a_4143_;
v___y_4156_ = v_a_4144_;
v___y_4157_ = v_a_4145_;
goto v___jp_4151_;
}
else
{
lean_object* v_cls_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v_cls_4218_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4219_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4148_, v_options_4147_, v___x_4219_);
if (v___x_4220_ == 0)
{
v___y_4152_ = v_a_4140_;
v___y_4153_ = v_a_4141_;
v___y_4154_ = v_a_4142_;
v___y_4155_ = v_a_4143_;
v___y_4156_ = v_a_4144_;
v___y_4157_ = v_a_4145_;
goto v___jp_4151_;
}
else
{
lean_object* v___x_4221_; size_t v_sz_4222_; size_t v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4221_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4222_ = lean_array_size(v_coinductiveElabData_4139_);
v___x_4223_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4139_);
v___x_4224_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4222_, v___x_4223_, v_coinductiveElabData_4139_);
v___x_4225_ = lean_array_to_list(v___x_4224_);
v___x_4226_ = lean_box(0);
v___x_4227_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4225_, v___x_4226_);
v___x_4228_ = l_Lean_MessageData_ofList(v___x_4227_);
v___x_4229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4221_);
lean_ctor_set(v___x_4229_, 1, v___x_4228_);
v___x_4230_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4218_, v___x_4229_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_dec_ref_known(v___x_4230_, 1);
v___y_4152_ = v_a_4140_;
v___y_4153_ = v_a_4141_;
v___y_4154_ = v_a_4142_;
v___y_4155_ = v_a_4143_;
v___y_4156_ = v_a_4144_;
v___y_4157_ = v_a_4145_;
goto v___jp_4151_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4139_);
return v___x_4230_;
}
}
}
v___jp_4151_:
{
size_t v_sz_4158_; size_t v___x_4159_; lean_object* v___x_4160_; 
v_sz_4158_ = lean_array_size(v_coinductiveElabData_4139_);
v___x_4159_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4139_);
v___x_4160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4158_, v___x_4159_, v_coinductiveElabData_4139_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v_toConstantVal_4164_; lean_object* v_numParams_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; size_t v_sz_4168_; lean_object* v___x_4169_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc_n(v_a_4161_, 2);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = lean_unsigned_to_nat(0u);
v___x_4163_ = lean_array_get_borrowed(v___x_4150_, v_a_4161_, v___x_4162_);
v_toConstantVal_4164_ = lean_ctor_get(v___x_4163_, 0);
v_numParams_4165_ = lean_ctor_get(v___x_4163_, 1);
v___x_4166_ = lean_array_get_size(v_a_4161_);
v___x_4167_ = lean_nat_sub(v_numParams_4165_, v___x_4166_);
v_sz_4168_ = lean_array_size(v_a_4161_);
lean_inc(v___x_4167_);
v___x_4169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4167_, v_sz_4168_, v___x_4159_, v_a_4161_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_object* v_a_4170_; lean_object* v_levelParams_4171_; lean_object* v_type_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; size_t v_sz_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___f_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___x_4182_; 
v_a_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc_n(v_a_4170_, 2);
lean_dec_ref_known(v___x_4169_, 1);
v_levelParams_4171_ = lean_ctor_get(v_toConstantVal_4164_, 1);
v_type_4172_ = lean_ctor_get(v_toConstantVal_4164_, 2);
v___x_4173_ = lean_box(0);
lean_inc(v_levelParams_4171_);
v___x_4174_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4171_, v___x_4173_);
v_sz_4175_ = lean_array_size(v_a_4170_);
lean_inc(v___x_4174_);
v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4174_, v_sz_4175_, v___x_4159_, v_a_4170_);
v___x_4177_ = lean_box_usize(v_sz_4168_);
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4161_);
v___f_4179_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4179_, 0, v___x_4174_);
lean_closure_set(v___f_4179_, 1, v___x_4176_);
lean_closure_set(v___f_4179_, 2, v___x_4177_);
lean_closure_set(v___f_4179_, 3, v___x_4178_);
lean_closure_set(v___f_4179_, 4, v_a_4161_);
lean_inc(v___x_4167_);
v___x_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4167_);
v___x_4181_ = 0;
lean_inc_ref(v_type_4172_);
v___x_4182_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4172_, v___x_4180_, v___f_4179_, v___x_4181_, v___x_4181_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v_lctx_4184_; lean_object* v_localInstances_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v_a_4183_ = lean_ctor_get(v___x_4182_, 0);
lean_inc(v_a_4183_);
lean_dec_ref_known(v___x_4182_, 1);
v_lctx_4184_ = lean_ctor_get(v___y_4154_, 2);
v_localInstances_4185_ = lean_ctor_get(v___y_4154_, 3);
v___x_4186_ = lean_array_get_size(v_a_4183_);
v___x_4187_ = lean_mk_empty_array_with_capacity(v___x_4186_);
lean_inc(v_levelParams_4171_);
v___x_4188_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4139_, v_a_4170_, v_levelParams_4171_, v_a_4183_, v___x_4186_, v___x_4162_, v___x_4187_);
lean_dec(v_a_4183_);
lean_dec(v_a_4170_);
lean_inc_ref(v_localInstances_4185_);
lean_inc_ref(v_lctx_4184_);
v___x_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4189_, 0, v_lctx_4184_);
lean_ctor_set(v___x_4189_, 1, v_localInstances_4185_);
v___x_4190_ = l_Lean_Elab_partialFixpoint(v___x_4189_, v___x_4188_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v___x_4191_; 
lean_dec_ref_known(v___x_4190_, 1);
lean_inc(v_a_4161_);
v___x_4191_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4161_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v___x_4192_; 
lean_dec_ref_known(v___x_4191_, 1);
lean_inc(v_a_4161_);
v___x_4192_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4167_, v_a_4161_, v_coinductiveElabData_4139_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
if (lean_obj_tag(v___x_4192_) == 0)
{
lean_object* v___x_4193_; 
lean_dec_ref_known(v___x_4192_, 1);
v___x_4193_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4161_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
return v___x_4193_;
}
else
{
lean_dec(v_a_4161_);
return v___x_4192_;
}
}
else
{
lean_dec(v___x_4167_);
lean_dec(v_a_4161_);
lean_dec_ref(v_coinductiveElabData_4139_);
return v___x_4191_;
}
}
else
{
lean_dec(v___x_4167_);
lean_dec(v_a_4161_);
lean_dec_ref(v_coinductiveElabData_4139_);
return v___x_4190_;
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec(v_a_4170_);
lean_dec(v___x_4167_);
lean_dec(v_a_4161_);
lean_dec_ref(v_coinductiveElabData_4139_);
v_a_4194_ = lean_ctor_get(v___x_4182_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4182_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4182_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4182_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
lean_dec(v___x_4167_);
lean_dec(v_a_4161_);
lean_dec_ref(v_coinductiveElabData_4139_);
v_a_4202_ = lean_ctor_get(v___x_4169_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4169_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4169_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_dec_ref(v_coinductiveElabData_4139_);
v_a_4210_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4160_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4160_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_);
lean_dec(v_a_4237_);
lean_dec_ref(v_a_4236_);
lean_dec(v_a_4235_);
lean_dec_ref(v_a_4234_);
lean_dec(v_a_4233_);
lean_dec_ref(v_a_4232_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4240_, lean_object* v___x_4241_, lean_object* v_params_4242_, size_t v_sz_4243_, size_t v_i_4244_, lean_object* v_bs_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4240_, v___x_4241_, v_params_4242_, v_sz_4243_, v_i_4244_, v_bs_4245_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4254_, lean_object* v___x_4255_, lean_object* v_params_4256_, lean_object* v_sz_4257_, lean_object* v_i_4258_, lean_object* v_bs_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
size_t v_sz_boxed_4267_; size_t v_i_boxed_4268_; lean_object* v_res_4269_; 
v_sz_boxed_4267_ = lean_unbox_usize(v_sz_4257_);
lean_dec(v_sz_4257_);
v_i_boxed_4268_ = lean_unbox_usize(v_i_4258_);
lean_dec(v_i_4258_);
v_res_4269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4254_, v___x_4255_, v_params_4256_, v_sz_boxed_4267_, v_i_boxed_4268_, v_bs_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4270_, lean_object* v_a_4271_, lean_object* v___x_4272_, lean_object* v_as_4273_, lean_object* v_i_4274_, lean_object* v_j_4275_, lean_object* v_inv_4276_, lean_object* v_bs_4277_){
_start:
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4270_, v_a_4271_, v___x_4272_, v_as_4273_, v_i_4274_, v_j_4275_, v_bs_4277_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4279_, lean_object* v_a_4280_, lean_object* v___x_4281_, lean_object* v_as_4282_, lean_object* v_i_4283_, lean_object* v_j_4284_, lean_object* v_inv_4285_, lean_object* v_bs_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4279_, v_a_4280_, v___x_4281_, v_as_4282_, v_i_4283_, v_j_4284_, v_inv_4285_, v_bs_4286_);
lean_dec_ref(v_as_4282_);
lean_dec_ref(v_a_4280_);
lean_dec_ref(v_coinductiveElabData_4279_);
return v_res_4287_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_PartialFixpoint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_UnusedVariables(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Coinductive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
