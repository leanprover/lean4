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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_liftCommandElabM___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "did not generate unfolding theorem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "existential_equiv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 65, 32, 87, 61, 118, 240, 105)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "functor_unfold"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 202, 245, 227, 23, 206, 217, 112)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "res: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "The conclusion of the constructor "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__2;
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " is "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "The elaborated constructor is of the type: "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Generating constructor: "};
static const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1;
static const lean_ctor_object l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Expected one argument"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "cases_eliminator"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(244, 14, 239, 189, 147, 54, 173, 250)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "elab_as_elim"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 49, 111, 107, 153, 28, 187, 88)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__7_value;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__4_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__7_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "expected to be quantifier"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object**);
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
v___x_107_ = lean_panic_fn(v___x_106_, v_msg_105_);
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
lean_dec_ref(v_x_117_);
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
lean_dec_ref(v___x_137_);
v___x_139_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v_goal_129_);
v___x_140_ = l_Lean_MVarId_rewrite(v_goal_129_, v_a_138_, v_eq_130_, v_symm_131_, v___x_139_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v_eNew_142_; lean_object* v_eqProof_143_; lean_object* v___x_144_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref(v___x_140_);
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
lean_inc_ref(v_env_314_);
lean_dec(v___x_302_);
lean_inc_ref(v_env_314_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg(lean_object* v_cls_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_options_353_; uint8_t v_hasTrace_354_; 
v_options_353_ = lean_ctor_get(v___y_351_, 2);
v_hasTrace_354_ = lean_ctor_get_uint8(v_options_353_, sizeof(void*)*1);
if (v_hasTrace_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_dec(v_cls_350_);
v___x_355_ = lean_box(v_hasTrace_354_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
else
{
lean_object* v_inheritedTraceOptions_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v_inheritedTraceOptions_357_ = lean_ctor_get(v___y_351_, 13);
v___x_358_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__1));
v___x_359_ = l_Lean_Name_append(v___x_358_, v_cls_350_);
v___x_360_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_357_, v_options_353_, v___x_359_);
lean_dec(v___x_359_);
v___x_361_ = lean_box(v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___boxed(lean_object* v_cls_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg(v_cls_363_, v___y_364_);
lean_dec_ref(v___y_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg(v_cls_367_, v___y_370_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object* v_cls_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
if (lean_obj_tag(v_a_381_) == 0)
{
lean_object* v___x_383_; 
v___x_383_ = l_List_reverse___redArg(v_a_382_);
return v___x_383_;
}
else
{
lean_object* v_head_384_; lean_object* v_tail_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_394_; 
v_head_384_ = lean_ctor_get(v_a_381_, 0);
v_tail_385_ = lean_ctor_get(v_a_381_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_a_381_);
if (v_isSharedCheck_394_ == 0)
{
v___x_387_ = v_a_381_;
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_tail_385_);
lean_inc(v_head_384_);
lean_dec(v_a_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_394_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_391_; 
v___x_389_ = l_Lean_mkLevelParam(v_head_384_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_a_382_);
lean_ctor_set(v___x_387_, 0, v___x_389_);
v___x_391_ = v___x_387_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v___x_389_);
lean_ctor_set(v_reuseFailAlloc_393_, 1, v_a_382_);
v___x_391_ = v_reuseFailAlloc_393_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
v_a_381_ = v_tail_385_;
v_a_382_ = v___x_391_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object* v_msgData_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; lean_object* v_env_402_; lean_object* v___x_403_; lean_object* v_mctx_404_; lean_object* v_lctx_405_; lean_object* v_options_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_401_ = lean_st_ref_get(v___y_399_);
v_env_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc_ref(v_env_402_);
lean_dec(v___x_401_);
v___x_403_ = lean_st_ref_get(v___y_397_);
v_mctx_404_ = lean_ctor_get(v___x_403_, 0);
lean_inc_ref(v_mctx_404_);
lean_dec(v___x_403_);
v_lctx_405_ = lean_ctor_get(v___y_396_, 2);
v_options_406_ = lean_ctor_get(v___y_398_, 2);
lean_inc_ref(v_options_406_);
lean_inc_ref(v_lctx_405_);
v___x_407_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_407_, 0, v_env_402_);
lean_ctor_set(v___x_407_, 1, v_mctx_404_);
lean_ctor_set(v___x_407_, 2, v_lctx_405_);
lean_ctor_set(v___x_407_, 3, v_options_406_);
v___x_408_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v_msgData_395_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_416_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0(void){
_start:
{
lean_object* v___x_417_; double v___x_418_; 
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_float_of_nat(v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object* v_cls_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_ref_429_; lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_475_; 
v_ref_429_ = lean_ctor_get(v___y_426_, 5);
v___x_430_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
v_isSharedCheck_475_ = !lean_is_exclusive(v___x_430_);
if (v_isSharedCheck_475_ == 0)
{
v___x_433_ = v___x_430_;
v_isShared_434_ = v_isSharedCheck_475_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_a_431_);
lean_dec(v___x_430_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_475_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___x_435_; lean_object* v_traceState_436_; lean_object* v_env_437_; lean_object* v_nextMacroScope_438_; lean_object* v_ngen_439_; lean_object* v_auxDeclNGen_440_; lean_object* v_cache_441_; lean_object* v_messages_442_; lean_object* v_infoState_443_; lean_object* v_snapshotTasks_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_474_; 
v___x_435_ = lean_st_ref_take(v___y_427_);
v_traceState_436_ = lean_ctor_get(v___x_435_, 4);
v_env_437_ = lean_ctor_get(v___x_435_, 0);
v_nextMacroScope_438_ = lean_ctor_get(v___x_435_, 1);
v_ngen_439_ = lean_ctor_get(v___x_435_, 2);
v_auxDeclNGen_440_ = lean_ctor_get(v___x_435_, 3);
v_cache_441_ = lean_ctor_get(v___x_435_, 5);
v_messages_442_ = lean_ctor_get(v___x_435_, 6);
v_infoState_443_ = lean_ctor_get(v___x_435_, 7);
v_snapshotTasks_444_ = lean_ctor_get(v___x_435_, 8);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_474_ == 0)
{
v___x_446_ = v___x_435_;
v_isShared_447_ = v_isSharedCheck_474_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_snapshotTasks_444_);
lean_inc(v_infoState_443_);
lean_inc(v_messages_442_);
lean_inc(v_cache_441_);
lean_inc(v_traceState_436_);
lean_inc(v_auxDeclNGen_440_);
lean_inc(v_ngen_439_);
lean_inc(v_nextMacroScope_438_);
lean_inc(v_env_437_);
lean_dec(v___x_435_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_474_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint64_t v_tid_448_; lean_object* v_traces_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_473_; 
v_tid_448_ = lean_ctor_get_uint64(v_traceState_436_, sizeof(void*)*1);
v_traces_449_ = lean_ctor_get(v_traceState_436_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_traceState_436_);
if (v_isSharedCheck_473_ == 0)
{
v___x_451_ = v_traceState_436_;
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_traces_449_);
lean_dec(v_traceState_436_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_473_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; double v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0);
v___x_455_ = 0;
v___x_456_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_457_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_457_, 0, v_cls_422_);
lean_ctor_set(v___x_457_, 1, v___x_453_);
lean_ctor_set(v___x_457_, 2, v___x_456_);
lean_ctor_set_float(v___x_457_, sizeof(void*)*3, v___x_454_);
lean_ctor_set_float(v___x_457_, sizeof(void*)*3 + 8, v___x_454_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*3 + 16, v___x_455_);
v___x_458_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2));
v___x_459_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_459_, 0, v___x_457_);
lean_ctor_set(v___x_459_, 1, v_a_431_);
lean_ctor_set(v___x_459_, 2, v___x_458_);
lean_inc(v_ref_429_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_ref_429_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = l_Lean_PersistentArray_push___redArg(v_traces_449_, v___x_460_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_461_);
v___x_463_ = v___x_451_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_461_);
lean_ctor_set_uint64(v_reuseFailAlloc_472_, sizeof(void*)*1, v_tid_448_);
v___x_463_ = v_reuseFailAlloc_472_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_465_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 4, v___x_463_);
v___x_465_ = v___x_446_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_env_437_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_nextMacroScope_438_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_ngen_439_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_auxDeclNGen_440_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v_cache_441_);
lean_ctor_set(v_reuseFailAlloc_471_, 6, v_messages_442_);
lean_ctor_set(v_reuseFailAlloc_471_, 7, v_infoState_443_);
lean_ctor_set(v_reuseFailAlloc_471_, 8, v_snapshotTasks_444_);
v___x_465_ = v_reuseFailAlloc_471_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_466_ = lean_st_ref_set(v___y_427_, v___x_465_);
v___x_467_ = lean_box(0);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 0, v___x_467_);
v___x_469_ = v___x_433_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_467_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object* v_cls_476_, lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_cls_476_, v_msg_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13_spec__14___redArg(lean_object* v_x_484_, lean_object* v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
lean_object* v_ks_488_; lean_object* v_vs_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
v_ks_488_ = lean_ctor_get(v_x_484_, 0);
v_vs_489_ = lean_ctor_get(v_x_484_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v_x_484_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_vs_489_);
lean_inc(v_ks_488_);
lean_dec(v_x_484_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_array_get_size(v_ks_488_);
v___x_494_ = lean_nat_dec_lt(v_x_485_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_dec(v_x_485_);
v___x_495_ = lean_array_push(v_ks_488_, v_x_486_);
v___x_496_ = lean_array_push(v_vs_489_, v_x_487_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_496_);
lean_ctor_set(v___x_491_, 0, v___x_495_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v___x_496_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
lean_object* v_k_x27_500_; uint8_t v___x_501_; 
v_k_x27_500_ = lean_array_fget_borrowed(v_ks_488_, v_x_485_);
v___x_501_ = l_Lean_instBEqMVarId_beq(v_x_486_, v_k_x27_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_503_; 
if (v_isShared_492_ == 0)
{
v___x_503_ = v___x_491_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_ks_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_vs_489_);
v___x_503_ = v_reuseFailAlloc_507_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(1u);
v___x_505_ = lean_nat_add(v_x_485_, v___x_504_);
lean_dec(v_x_485_);
v_x_484_ = v___x_503_;
v_x_485_ = v___x_505_;
goto _start;
}
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_508_ = lean_array_fset(v_ks_488_, v_x_485_, v_x_486_);
v___x_509_ = lean_array_fset(v_vs_489_, v_x_485_, v_x_487_);
lean_dec(v_x_485_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v___x_509_);
lean_ctor_set(v___x_491_, 0, v___x_508_);
v___x_511_ = v___x_491_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13___redArg(lean_object* v_n_514_, lean_object* v_k_515_, lean_object* v_v_516_){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13_spec__14___redArg(v_n_514_, v___x_517_, v_k_515_, v_v_516_);
return v___x_518_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__0(void){
_start:
{
size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; 
v___x_519_ = ((size_t)5ULL);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_shift_left(v___x_520_, v___x_519_);
return v___x_521_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; 
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__0);
v___x_524_ = lean_usize_sub(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg(lean_object* v_x_526_, size_t v_x_527_, size_t v_x_528_, lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v_es_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; lean_object* v_j_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_es_531_ = lean_ctor_get(v_x_526_, 0);
v___x_532_ = ((size_t)5ULL);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__1);
v___x_535_ = lean_usize_land(v_x_527_, v___x_534_);
v_j_536_ = lean_usize_to_nat(v___x_535_);
v___x_537_ = lean_array_get_size(v_es_531_);
v___x_538_ = lean_nat_dec_lt(v_j_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v_j_536_);
lean_dec(v_x_530_);
lean_dec(v_x_529_);
return v_x_526_;
}
else
{
lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_575_; 
lean_inc_ref(v_es_531_);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_x_526_, 0);
lean_dec(v_unused_576_);
v___x_540_ = v_x_526_;
v_isShared_541_ = v_isSharedCheck_575_;
goto v_resetjp_539_;
}
else
{
lean_dec(v_x_526_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_575_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_v_542_; lean_object* v___x_543_; lean_object* v_xs_x27_544_; lean_object* v___y_546_; 
v_v_542_ = lean_array_fget(v_es_531_, v_j_536_);
v___x_543_ = lean_box(0);
v_xs_x27_544_ = lean_array_fset(v_es_531_, v_j_536_, v___x_543_);
switch(lean_obj_tag(v_v_542_))
{
case 0:
{
lean_object* v_key_551_; lean_object* v_val_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_562_; 
v_key_551_ = lean_ctor_get(v_v_542_, 0);
v_val_552_ = lean_ctor_get(v_v_542_, 1);
v_isSharedCheck_562_ = !lean_is_exclusive(v_v_542_);
if (v_isSharedCheck_562_ == 0)
{
v___x_554_ = v_v_542_;
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_val_552_);
lean_inc(v_key_551_);
lean_dec(v_v_542_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_562_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
uint8_t v___x_556_; 
v___x_556_ = l_Lean_instBEqMVarId_beq(v_x_529_, v_key_551_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_del_object(v___x_554_);
v___x_557_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_551_, v_val_552_, v_x_529_, v_x_530_);
v___x_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
v___y_546_ = v___x_558_;
goto v___jp_545_;
}
else
{
lean_object* v___x_560_; 
lean_dec(v_val_552_);
lean_dec(v_key_551_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_x_530_);
lean_ctor_set(v___x_554_, 0, v_x_529_);
v___x_560_ = v___x_554_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_x_529_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_x_530_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
v___y_546_ = v___x_560_;
goto v___jp_545_;
}
}
}
}
case 1:
{
lean_object* v_node_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_573_; 
v_node_563_ = lean_ctor_get(v_v_542_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v_v_542_);
if (v_isSharedCheck_573_ == 0)
{
v___x_565_ = v_v_542_;
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_node_563_);
lean_dec(v_v_542_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_573_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_567_ = lean_usize_shift_right(v_x_527_, v___x_532_);
v___x_568_ = lean_usize_add(v_x_528_, v___x_533_);
v___x_569_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg(v_node_563_, v___x_567_, v___x_568_, v_x_529_, v_x_530_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_569_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
v___y_546_ = v___x_571_;
goto v___jp_545_;
}
}
}
default: 
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_574_, 0, v_x_529_);
lean_ctor_set(v___x_574_, 1, v_x_530_);
v___y_546_ = v___x_574_;
goto v___jp_545_;
}
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_547_ = lean_array_fset(v_xs_x27_544_, v_j_536_, v___y_546_);
lean_dec(v_j_536_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_547_);
v___x_549_ = v___x_540_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
else
{
lean_object* v_ks_577_; lean_object* v_vs_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_598_; 
v_ks_577_ = lean_ctor_get(v_x_526_, 0);
v_vs_578_ = lean_ctor_get(v_x_526_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_526_);
if (v_isSharedCheck_598_ == 0)
{
v___x_580_ = v_x_526_;
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_vs_578_);
lean_inc(v_ks_577_);
lean_dec(v_x_526_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_ks_577_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_vs_578_);
v___x_583_ = v_reuseFailAlloc_597_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v_newNode_584_; uint8_t v___y_586_; size_t v___x_592_; uint8_t v___x_593_; 
v_newNode_584_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13___redArg(v___x_583_, v_x_529_, v_x_530_);
v___x_592_ = ((size_t)7ULL);
v___x_593_ = lean_usize_dec_le(v___x_592_, v_x_528_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_584_);
v___x_595_ = lean_unsigned_to_nat(4u);
v___x_596_ = lean_nat_dec_lt(v___x_594_, v___x_595_);
lean_dec(v___x_594_);
v___y_586_ = v___x_596_;
goto v___jp_585_;
}
else
{
v___y_586_ = v___x_593_;
goto v___jp_585_;
}
v___jp_585_:
{
if (v___y_586_ == 0)
{
lean_object* v_ks_587_; lean_object* v_vs_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_ks_587_ = lean_ctor_get(v_newNode_584_, 0);
lean_inc_ref(v_ks_587_);
v_vs_588_ = lean_ctor_get(v_newNode_584_, 1);
lean_inc_ref(v_vs_588_);
lean_dec_ref(v_newNode_584_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___closed__2);
v___x_591_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___redArg(v_x_528_, v_ks_587_, v_vs_588_, v___x_589_, v___x_590_);
lean_dec_ref(v_vs_588_);
lean_dec_ref(v_ks_587_);
return v___x_591_;
}
else
{
return v_newNode_584_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___redArg(size_t v_depth_599_, lean_object* v_keys_600_, lean_object* v_vals_601_, lean_object* v_i_602_, lean_object* v_entries_603_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = lean_array_get_size(v_keys_600_);
v___x_605_ = lean_nat_dec_lt(v_i_602_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_i_602_);
return v_entries_603_;
}
else
{
lean_object* v_k_606_; lean_object* v_v_607_; uint64_t v___x_608_; size_t v_h_609_; size_t v___x_610_; lean_object* v___x_611_; size_t v___x_612_; size_t v___x_613_; size_t v___x_614_; size_t v_h_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_k_606_ = lean_array_fget_borrowed(v_keys_600_, v_i_602_);
v_v_607_ = lean_array_fget_borrowed(v_vals_601_, v_i_602_);
v___x_608_ = l_Lean_instHashableMVarId_hash(v_k_606_);
v_h_609_ = lean_uint64_to_usize(v___x_608_);
v___x_610_ = ((size_t)5ULL);
v___x_611_ = lean_unsigned_to_nat(1u);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_sub(v_depth_599_, v___x_612_);
v___x_614_ = lean_usize_mul(v___x_610_, v___x_613_);
v_h_615_ = lean_usize_shift_right(v_h_609_, v___x_614_);
v___x_616_ = lean_nat_add(v_i_602_, v___x_611_);
lean_dec(v_i_602_);
lean_inc(v_v_607_);
lean_inc(v_k_606_);
v___x_617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg(v_entries_603_, v_h_615_, v_depth_599_, v_k_606_, v_v_607_);
v_i_602_ = v___x_616_;
v_entries_603_ = v___x_617_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_depth_619_, lean_object* v_keys_620_, lean_object* v_vals_621_, lean_object* v_i_622_, lean_object* v_entries_623_){
_start:
{
size_t v_depth_boxed_624_; lean_object* v_res_625_; 
v_depth_boxed_624_ = lean_unbox_usize(v_depth_619_);
lean_dec(v_depth_619_);
v_res_625_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___redArg(v_depth_boxed_624_, v_keys_620_, v_vals_621_, v_i_622_, v_entries_623_);
lean_dec_ref(v_vals_621_);
lean_dec_ref(v_keys_620_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg___boxed(lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
size_t v_x_8766__boxed_631_; size_t v_x_8767__boxed_632_; lean_object* v_res_633_; 
v_x_8766__boxed_631_ = lean_unbox_usize(v_x_627_);
lean_dec(v_x_627_);
v_x_8767__boxed_632_ = lean_unbox_usize(v_x_628_);
lean_dec(v_x_628_);
v_res_633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg(v_x_626_, v_x_8766__boxed_631_, v_x_8767__boxed_632_, v_x_629_, v_x_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
uint64_t v___x_637_; size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_637_ = l_Lean_instHashableMVarId_hash(v_x_635_);
v___x_638_ = lean_uint64_to_usize(v___x_637_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg(v_x_634_, v___x_638_, v___x_639_, v_x_635_, v_x_636_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object* v_mvarId_641_, lean_object* v_val_642_, lean_object* v___y_643_){
_start:
{
lean_object* v___x_645_; lean_object* v_mctx_646_; lean_object* v_cache_647_; lean_object* v_zetaDeltaFVarIds_648_; lean_object* v_postponed_649_; lean_object* v_diag_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_677_; 
v___x_645_ = lean_st_ref_take(v___y_643_);
v_mctx_646_ = lean_ctor_get(v___x_645_, 0);
v_cache_647_ = lean_ctor_get(v___x_645_, 1);
v_zetaDeltaFVarIds_648_ = lean_ctor_get(v___x_645_, 2);
v_postponed_649_ = lean_ctor_get(v___x_645_, 3);
v_diag_650_ = lean_ctor_get(v___x_645_, 4);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_677_ == 0)
{
v___x_652_ = v___x_645_;
v_isShared_653_ = v_isSharedCheck_677_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_diag_650_);
lean_inc(v_postponed_649_);
lean_inc(v_zetaDeltaFVarIds_648_);
lean_inc(v_cache_647_);
lean_inc(v_mctx_646_);
lean_dec(v___x_645_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_677_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_depth_654_; lean_object* v_levelAssignDepth_655_; lean_object* v_mvarCounter_656_; lean_object* v_lDepth_657_; lean_object* v_decls_658_; lean_object* v_userNames_659_; lean_object* v_lAssignment_660_; lean_object* v_eAssignment_661_; lean_object* v_dAssignment_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_676_; 
v_depth_654_ = lean_ctor_get(v_mctx_646_, 0);
v_levelAssignDepth_655_ = lean_ctor_get(v_mctx_646_, 1);
v_mvarCounter_656_ = lean_ctor_get(v_mctx_646_, 2);
v_lDepth_657_ = lean_ctor_get(v_mctx_646_, 3);
v_decls_658_ = lean_ctor_get(v_mctx_646_, 4);
v_userNames_659_ = lean_ctor_get(v_mctx_646_, 5);
v_lAssignment_660_ = lean_ctor_get(v_mctx_646_, 6);
v_eAssignment_661_ = lean_ctor_get(v_mctx_646_, 7);
v_dAssignment_662_ = lean_ctor_get(v_mctx_646_, 8);
v_isSharedCheck_676_ = !lean_is_exclusive(v_mctx_646_);
if (v_isSharedCheck_676_ == 0)
{
v___x_664_ = v_mctx_646_;
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_dAssignment_662_);
lean_inc(v_eAssignment_661_);
lean_inc(v_lAssignment_660_);
lean_inc(v_userNames_659_);
lean_inc(v_decls_658_);
lean_inc(v_lDepth_657_);
lean_inc(v_mvarCounter_656_);
lean_inc(v_levelAssignDepth_655_);
lean_inc(v_depth_654_);
lean_dec(v_mctx_646_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_676_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_661_, v_mvarId_641_, v_val_642_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 7, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_depth_654_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_levelAssignDepth_655_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_mvarCounter_656_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_lDepth_657_);
lean_ctor_set(v_reuseFailAlloc_675_, 4, v_decls_658_);
lean_ctor_set(v_reuseFailAlloc_675_, 5, v_userNames_659_);
lean_ctor_set(v_reuseFailAlloc_675_, 6, v_lAssignment_660_);
lean_ctor_set(v_reuseFailAlloc_675_, 7, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_675_, 8, v_dAssignment_662_);
v___x_668_ = v_reuseFailAlloc_675_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_668_);
v___x_670_ = v___x_652_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_cache_647_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_zetaDeltaFVarIds_648_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_postponed_649_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_diag_650_);
v___x_670_ = v_reuseFailAlloc_674_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_st_ref_set(v___y_643_, v___x_670_);
v___x_672_ = lean_box(0);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object* v_mvarId_678_, lean_object* v_val_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_678_, v_val_679_, v___y_680_);
lean_dec(v___y_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_ref_689_; lean_object* v___x_690_; lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_699_; 
v_ref_689_ = lean_ctor_get(v___y_686_, 5);
v___x_690_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_699_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_699_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
lean_inc(v_ref_689_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_ref_689_);
lean_ctor_set(v___x_695_, 1, v_a_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 1);
lean_ctor_set(v___x_693_, 0, v___x_695_);
v___x_697_ = v___x_693_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
lean_dec(v___y_704_);
lean_dec_ref(v___y_703_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_array_714_; lean_object* v_start_715_; lean_object* v_stop_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_731_; 
v_array_714_ = lean_ctor_get(v_a_707_, 0);
v_start_715_ = lean_ctor_get(v_a_707_, 1);
v_stop_716_ = lean_ctor_get(v_a_707_, 2);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_707_);
if (v_isSharedCheck_731_ == 0)
{
v___x_718_ = v_a_707_;
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_stop_716_);
lean_inc(v_start_715_);
lean_inc(v_array_714_);
lean_dec(v_a_707_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_731_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
uint8_t v___x_720_; 
v___x_720_ = lean_nat_dec_lt(v_start_715_, v_stop_716_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_del_object(v___x_718_);
lean_dec(v_stop_716_);
lean_dec(v_start_715_);
lean_dec_ref(v_array_714_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_b_708_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_array_fget_borrowed(v_array_714_, v_start_715_);
lean_inc(v___x_722_);
v___x_723_ = l_Lean_Meta_mkCongrFun(v_b_708_, v___x_722_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_728_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = lean_nat_add(v_start_715_, v___x_725_);
lean_dec(v_start_715_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 1, v___x_726_);
v___x_728_ = v___x_718_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_array_714_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_stop_716_);
v___x_728_ = v_reuseFailAlloc_730_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
v_a_707_ = v___x_728_;
v_b_708_ = v_a_724_;
goto _start;
}
}
else
{
lean_del_object(v___x_718_);
lean_dec(v_stop_716_);
lean_dec(v_start_715_);
lean_dec_ref(v_array_714_);
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_732_, lean_object* v_b_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_732_, v_b_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_740_, lean_object* v___x_741_, size_t v_sz_742_, size_t v_i_743_, lean_object* v_bs_744_){
_start:
{
uint8_t v___x_745_; 
v___x_745_ = lean_usize_dec_lt(v_i_743_, v_sz_742_);
if (v___x_745_ == 0)
{
lean_dec(v_levels_740_);
return v_bs_744_;
}
else
{
lean_object* v_v_746_; lean_object* v_toConstantVal_747_; lean_object* v_name_748_; lean_object* v___x_749_; lean_object* v_bs_x27_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v_v_746_ = lean_array_uget_borrowed(v_bs_744_, v_i_743_);
v_toConstantVal_747_ = lean_ctor_get(v_v_746_, 0);
v_name_748_ = lean_ctor_get(v_toConstantVal_747_, 0);
lean_inc(v_name_748_);
v___x_749_ = lean_unsigned_to_nat(0u);
v_bs_x27_750_ = lean_array_uset(v_bs_744_, v_i_743_, v___x_749_);
v___x_751_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_748_);
lean_inc(v_levels_740_);
v___x_752_ = l_Lean_mkConst(v___x_751_, v_levels_740_);
v___x_753_ = l_Lean_mkAppN(v___x_752_, v___x_741_);
v___x_754_ = ((size_t)1ULL);
v___x_755_ = lean_usize_add(v_i_743_, v___x_754_);
v___x_756_ = lean_array_uset(v_bs_x27_750_, v_i_743_, v___x_753_);
v_i_743_ = v___x_755_;
v_bs_744_ = v___x_756_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_758_, lean_object* v___x_759_, lean_object* v_sz_760_, lean_object* v_i_761_, lean_object* v_bs_762_){
_start:
{
size_t v_sz_boxed_763_; size_t v_i_boxed_764_; lean_object* v_res_765_; 
v_sz_boxed_763_ = lean_unbox_usize(v_sz_760_);
lean_dec(v_sz_760_);
v_i_boxed_764_ = lean_unbox_usize(v_i_761_);
lean_dec(v_i_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_758_, v___x_759_, v_sz_boxed_763_, v_i_boxed_764_, v_bs_762_);
lean_dec_ref(v___x_759_);
return v_res_765_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__1(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__0));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0(lean_object* v_infos_772_, lean_object* v_numParams_773_, lean_object* v___x_774_, lean_object* v_name_775_, lean_object* v_levels_776_, lean_object* v_args_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; size_t v_sz_795_; size_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_784_ = lean_array_get_size(v_infos_772_);
v___x_785_ = lean_nat_sub(v_numParams_773_, v___x_784_);
lean_inc(v___x_774_);
lean_inc_ref(v_args_777_);
v___x_786_ = l_Array_toSubarray___redArg(v_args_777_, v___x_774_, v___x_785_);
v___x_787_ = lean_array_get_size(v_args_777_);
v___x_788_ = l_Array_toSubarray___redArg(v_args_777_, v_numParams_773_, v___x_787_);
lean_inc(v_name_775_);
v___x_789_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_775_);
lean_inc(v_levels_776_);
lean_inc(v___x_789_);
v___x_790_ = l_Lean_mkConst(v___x_789_, v_levels_776_);
v___x_791_ = l_Subarray_copy___redArg(v___x_786_);
v___x_792_ = l_Lean_mkAppN(v___x_790_, v___x_791_);
lean_inc_ref(v___x_788_);
v___x_793_ = l_Subarray_copy___redArg(v___x_788_);
v___x_794_ = l_Lean_mkAppN(v___x_792_, v___x_793_);
v_sz_795_ = lean_array_size(v_infos_772_);
v___x_796_ = ((size_t)0ULL);
lean_inc(v_levels_776_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_776_, v___x_791_, v_sz_795_, v___x_796_, v_infos_772_);
lean_inc(v_levels_776_);
lean_inc(v_name_775_);
v___x_798_ = l_Lean_mkConst(v_name_775_, v_levels_776_);
lean_inc_ref(v___x_791_);
v___x_799_ = l_Array_append___redArg(v___x_791_, v___x_797_);
lean_dec_ref(v___x_797_);
v___x_800_ = l_Array_append___redArg(v___x_799_, v___x_793_);
v___x_801_ = l_Lean_mkAppN(v___x_798_, v___x_800_);
lean_dec_ref(v___x_800_);
v___x_802_ = l_Lean_Meta_mkEq(v___x_794_, v___x_801_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_869_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_869_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_869_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_869_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_808_; 
if (v_isShared_806_ == 0)
{
lean_ctor_set_tag(v___x_805_, 1);
v___x_808_ = v___x_805_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_803_);
v___x_808_ = v_reuseFailAlloc_868_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
uint8_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_809_ = 0;
v___x_810_ = lean_box(0);
v___x_811_ = l_Lean_Meta_mkFreshExprMVar(v___x_808_, v___x_809_, v___x_810_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_811_);
v___x_813_ = l_Lean_Meta_getEqnsFor_x3f(v___x_789_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___y_816_; lean_object* v___y_817_; lean_object* v___y_818_; lean_object* v___y_819_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
if (lean_obj_tag(v_a_814_) == 1)
{
lean_object* v_val_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_val_822_ = lean_ctor_get(v_a_814_, 0);
lean_inc(v_val_822_);
lean_dec_ref(v_a_814_);
v___x_823_ = lean_array_get_size(v_val_822_);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_dec_eq(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_dec(v_val_822_);
lean_dec(v_a_812_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
lean_dec_ref(v___x_788_);
lean_dec(v_levels_776_);
lean_dec(v_name_775_);
lean_dec(v___x_774_);
v___y_816_ = v___y_779_;
v___y_817_ = v___y_780_;
v___y_818_ = v___y_781_;
v___y_819_ = v___y_782_;
goto v___jp_815_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_826_ = lean_array_fget(v_val_822_, v___x_774_);
lean_dec(v___x_774_);
lean_dec(v_val_822_);
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__3));
v___x_828_ = l_Lean_Name_append(v_name_775_, v___x_827_);
lean_inc(v_levels_776_);
v___x_829_ = l_Lean_mkConst(v___x_828_, v_levels_776_);
v___x_830_ = l_Lean_mkConst(v___x_826_, v_levels_776_);
v___x_831_ = l_Lean_mkAppN(v___x_830_, v___x_791_);
v___x_832_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_788_, v___x_831_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_832_);
v___x_834_ = l_Lean_Expr_mvarId_x21(v_a_812_);
v___x_835_ = 0;
v___x_836_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_834_, v___x_829_, v___x_835_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref(v___x_836_);
v___x_838_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_837_, v_a_833_, v___y_780_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v___x_838_);
v___x_839_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_812_, v___y_780_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref(v___x_839_);
v___x_841_ = l_Array_append___redArg(v___x_791_, v___x_793_);
lean_dec_ref(v___x_793_);
v___x_842_ = 1;
v___x_843_ = l_Lean_Meta_mkLambdaFVars(v___x_841_, v_a_840_, v___x_835_, v___x_825_, v___x_835_, v___x_825_, v___x_842_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec_ref(v___x_841_);
return v___x_843_;
}
else
{
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
return v___x_839_;
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_a_812_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
v_a_844_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_838_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_838_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
lean_dec(v_a_833_);
lean_dec(v_a_812_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
v_a_852_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_836_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_836_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
else
{
lean_dec_ref(v___x_829_);
lean_dec(v_a_812_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
return v___x_832_;
}
}
}
else
{
lean_dec(v_a_814_);
lean_dec(v_a_812_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
lean_dec_ref(v___x_788_);
lean_dec(v_levels_776_);
lean_dec(v_name_775_);
lean_dec(v___x_774_);
v___y_816_ = v___y_779_;
v___y_817_ = v___y_780_;
v___y_818_ = v___y_781_;
v___y_819_ = v___y_782_;
goto v___jp_815_;
}
v___jp_815_:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___closed__1);
v___x_821_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_820_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
return v___x_821_;
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_a_812_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
lean_dec_ref(v___x_788_);
lean_dec(v_levels_776_);
lean_dec(v_name_775_);
lean_dec(v___x_774_);
v_a_860_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_813_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_813_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
lean_dec(v___x_789_);
lean_dec_ref(v___x_788_);
lean_dec(v_levels_776_);
lean_dec(v_name_775_);
lean_dec(v___x_774_);
return v___x_811_;
}
}
}
}
else
{
lean_dec_ref(v___x_793_);
lean_dec_ref(v___x_791_);
lean_dec(v___x_789_);
lean_dec_ref(v___x_788_);
lean_dec(v_levels_776_);
lean_dec(v_name_775_);
lean_dec(v___x_774_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___boxed(lean_object* v_infos_870_, lean_object* v_numParams_871_, lean_object* v___x_872_, lean_object* v_name_873_, lean_object* v_levels_874_, lean_object* v_args_875_, lean_object* v_x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0(v_infos_870_, v_numParams_871_, v___x_872_, v_name_873_, v_levels_874_, v_args_875_, v_x_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec_ref(v_x_876_);
return v_res_882_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__3(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__2));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10(lean_object* v_infos_889_, lean_object* v_levels_890_, lean_object* v_as_891_, size_t v_sz_892_, size_t v_i_893_, lean_object* v_b_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
uint8_t v___x_900_; 
v___x_900_ = lean_usize_dec_lt(v_i_893_, v_sz_892_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec(v_levels_890_);
lean_dec_ref(v_infos_889_);
v___x_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_901_, 0, v_b_894_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v_toConstantVal_903_; lean_object* v_numParams_904_; lean_object* v_name_905_; lean_object* v_levelParams_906_; lean_object* v_type_907_; lean_object* v___x_908_; lean_object* v___f_909_; uint8_t v___x_910_; lean_object* v___x_911_; 
v_a_902_ = lean_array_uget_borrowed(v_as_891_, v_i_893_);
v_toConstantVal_903_ = lean_ctor_get(v_a_902_, 0);
v_numParams_904_ = lean_ctor_get(v_a_902_, 1);
v_name_905_ = lean_ctor_get(v_toConstantVal_903_, 0);
v_levelParams_906_ = lean_ctor_get(v_toConstantVal_903_, 1);
v_type_907_ = lean_ctor_get(v_toConstantVal_903_, 2);
v___x_908_ = lean_unsigned_to_nat(0u);
lean_inc(v_levels_890_);
lean_inc(v_name_905_);
lean_inc(v_numParams_904_);
lean_inc_ref(v_infos_889_);
v___f_909_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___lam__0___boxed), 12, 5);
lean_closure_set(v___f_909_, 0, v_infos_889_);
lean_closure_set(v___f_909_, 1, v_numParams_904_);
lean_closure_set(v___f_909_, 2, v___x_908_);
lean_closure_set(v___f_909_, 3, v_name_905_);
lean_closure_set(v___f_909_, 4, v_levels_890_);
v___x_910_ = 0;
lean_inc_ref(v_type_907_);
v___x_911_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_907_, v___f_909_, v___x_910_, v___x_910_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref(v___x_911_);
v___x_913_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_914_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg(v___x_913_, v___y_897_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; uint8_t v___x_951_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_914_);
v___x_916_ = lean_box(0);
v___x_951_ = lean_unbox(v_a_915_);
lean_dec(v_a_915_);
if (v___x_951_ == 0)
{
v___y_918_ = v___y_895_;
v___y_919_ = v___y_896_;
v___y_920_ = v___y_897_;
v___y_921_ = v___y_898_;
goto v___jp_917_;
}
else
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_952_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__3);
lean_inc(v_a_912_);
v___x_953_ = l_Lean_MessageData_ofExpr(v_a_912_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v___x_913_, v___x_954_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_dec_ref(v___x_955_);
v___y_918_ = v___y_895_;
v___y_919_ = v___y_896_;
v___y_920_ = v___y_897_;
v___y_921_ = v___y_898_;
goto v___jp_917_;
}
else
{
lean_dec(v_a_912_);
lean_dec(v_levels_890_);
lean_dec_ref(v_infos_889_);
return v___x_955_;
}
}
v___jp_917_:
{
lean_object* v___x_922_; 
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
lean_inc(v_a_912_);
v___x_922_ = lean_infer_type(v_a_912_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_922_);
lean_inc(v_name_905_);
v___x_924_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_905_);
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__1));
v___x_926_ = l_Lean_Name_append(v___x_924_, v___x_925_);
v___x_927_ = lean_box(0);
lean_inc(v_levelParams_906_);
v___x_928_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_926_, v_levelParams_906_, v_a_923_, v_a_912_, v___x_927_, v___y_921_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
lean_dec_ref(v___x_928_);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v_a_929_);
v___x_931_ = l_Lean_addDecl(v___x_930_, v___x_910_, v___y_920_, v___y_921_);
if (lean_obj_tag(v___x_931_) == 0)
{
size_t v___x_932_; size_t v___x_933_; 
lean_dec_ref(v___x_931_);
v___x_932_ = ((size_t)1ULL);
v___x_933_ = lean_usize_add(v_i_893_, v___x_932_);
v_i_893_ = v___x_933_;
v_b_894_ = v___x_916_;
goto _start;
}
else
{
lean_dec(v_levels_890_);
lean_dec_ref(v_infos_889_);
return v___x_931_;
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_levels_890_);
lean_dec_ref(v_infos_889_);
v_a_935_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_928_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_928_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_a_912_);
lean_dec(v_levels_890_);
lean_dec_ref(v_infos_889_);
v_a_943_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_922_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_922_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_dec(v_a_912_);
lean_dec(v_levels_890_);
lean_dec_ref(v_infos_889_);
v_a_956_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_914_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_914_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
else
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
lean_dec(v_levels_890_);
lean_dec_ref(v_infos_889_);
v_a_964_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_971_ == 0)
{
v___x_966_ = v___x_911_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_911_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_a_964_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___boxed(lean_object* v_infos_972_, lean_object* v_levels_973_, lean_object* v_as_974_, lean_object* v_sz_975_, lean_object* v_i_976_, lean_object* v_b_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
size_t v_sz_boxed_983_; size_t v_i_boxed_984_; lean_object* v_res_985_; 
v_sz_boxed_983_ = lean_unbox_usize(v_sz_975_);
lean_dec(v_sz_975_);
v_i_boxed_984_ = lean_unbox_usize(v_i_976_);
lean_dec(v_i_976_);
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10(v_infos_972_, v_levels_973_, v_as_974_, v_sz_boxed_983_, v_i_boxed_984_, v_b_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec_ref(v_as_974_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object* v_infos_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v_toConstantVal_995_; lean_object* v_levelParams_996_; lean_object* v___x_997_; lean_object* v_levels_998_; lean_object* v___x_999_; size_t v_sz_1000_; size_t v___x_1001_; lean_object* v___x_1002_; 
v___x_992_ = l_Lean_instInhabitedInductiveVal_default;
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_borrowed(v___x_992_, v_infos_986_, v___x_993_);
v_toConstantVal_995_ = lean_ctor_get(v___x_994_, 0);
v_levelParams_996_ = lean_ctor_get(v_toConstantVal_995_, 1);
v___x_997_ = lean_box(0);
lean_inc(v_levelParams_996_);
v_levels_998_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_996_, v___x_997_);
v___x_999_ = lean_box(0);
v_sz_1000_ = lean_array_size(v_infos_986_);
v___x_1001_ = ((size_t)0ULL);
lean_inc_ref(v_infos_986_);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10(v_infos_986_, v_levels_998_, v_infos_986_, v_sz_1000_, v___x_1001_, v___x_999_, v_a_987_, v_a_988_, v_a_989_, v_a_990_);
lean_dec_ref(v_infos_986_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1009_ == 0)
{
lean_object* v_unused_1010_; 
v_unused_1010_ = lean_ctor_get(v___x_1002_, 0);
lean_dec(v_unused_1010_);
v___x_1004_ = v___x_1002_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_dec(v___x_1002_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_999_);
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_999_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object* v_infos_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object* v_00_u03b1_1018_, lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_1026_, v_msg_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object* v_inst_1034_, lean_object* v_R_1035_, lean_object* v_a_1036_, lean_object* v_b_1037_, lean_object* v_c_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_1036_, v_b_1037_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object* v_inst_1045_, lean_object* v_R_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_, lean_object* v_c_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_1045_, v_R_1046_, v_a_1047_, v_b_1048_, v_c_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object* v_mvarId_1056_, lean_object* v_val_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_1056_, v_val_1057_, v___y_1059_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object* v_mvarId_1064_, lean_object* v_val_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1064_, v_val_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object* v_00_u03b2_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_1073_, v_x_1074_, v_x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, size_t v_x_1079_, size_t v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___redArg(v_x_1078_, v_x_1079_, v_x_1080_, v_x_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10___boxed(lean_object* v_00_u03b2_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_){
_start:
{
size_t v_x_9574__boxed_1090_; size_t v_x_9575__boxed_1091_; lean_object* v_res_1092_; 
v_x_9574__boxed_1090_ = lean_unbox_usize(v_x_1086_);
lean_dec(v_x_1086_);
v_x_9575__boxed_1091_ = lean_unbox_usize(v_x_1087_);
lean_dec(v_x_1087_);
v_res_1092_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10(v_00_u03b2_1084_, v_x_1085_, v_x_9574__boxed_1090_, v_x_9575__boxed_1091_, v_x_1088_, v_x_1089_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13(lean_object* v_00_u03b2_1093_, lean_object* v_n_1094_, lean_object* v_k_1095_, lean_object* v_v_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13___redArg(v_n_1094_, v_k_1095_, v_v_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14(lean_object* v_00_u03b2_1098_, size_t v_depth_1099_, lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_heq_1102_, lean_object* v_i_1103_, lean_object* v_entries_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___redArg(v_depth_1099_, v_keys_1100_, v_vals_1101_, v_i_1103_, v_entries_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_depth_1107_, lean_object* v_keys_1108_, lean_object* v_vals_1109_, lean_object* v_heq_1110_, lean_object* v_i_1111_, lean_object* v_entries_1112_){
_start:
{
size_t v_depth_boxed_1113_; lean_object* v_res_1114_; 
v_depth_boxed_1113_ = lean_unbox_usize(v_depth_1107_);
lean_dec(v_depth_1107_);
v_res_1114_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__14(v_00_u03b2_1106_, v_depth_boxed_1113_, v_keys_1108_, v_vals_1109_, v_heq_1110_, v_i_1111_, v_entries_1112_);
lean_dec_ref(v_vals_1109_);
lean_dec_ref(v_keys_1108_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13_spec__14(lean_object* v_00_u03b2_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__10_spec__13_spec__14___redArg(v_x_1116_, v_x_1117_, v_x_1118_, v_x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_cls_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_options_1124_; uint8_t v_hasTrace_1125_; 
v_options_1124_ = lean_ctor_get(v___y_1122_, 2);
v_hasTrace_1125_ = lean_ctor_get_uint8(v_options_1124_, sizeof(void*)*1);
if (v_hasTrace_1125_ == 0)
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec(v_cls_1121_);
v___x_1126_ = lean_box(v_hasTrace_1125_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
else
{
lean_object* v_inheritedTraceOptions_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_inheritedTraceOptions_1128_ = lean_ctor_get(v___y_1122_, 13);
v___x_1129_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___redArg___closed__1));
v___x_1130_ = l_Lean_Name_append(v___x_1129_, v_cls_1121_);
v___x_1131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1128_, v_options_1124_, v___x_1130_);
lean_dec(v___x_1130_);
v___x_1132_ = lean_box(v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_cls_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_cls_1134_, v___y_1135_);
lean_dec_ref(v___y_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_cls_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_cls_1138_, v___y_1143_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_cls_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_cls_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_e_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v___x_1159_; 
v___x_1159_ = l_Lean_Expr_hasMVar(v_e_1156_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_e_1156_);
return v___x_1160_;
}
else
{
lean_object* v___x_1161_; lean_object* v_mctx_1162_; lean_object* v___x_1163_; lean_object* v_fst_1164_; lean_object* v_snd_1165_; lean_object* v___x_1166_; lean_object* v_cache_1167_; lean_object* v_zetaDeltaFVarIds_1168_; lean_object* v_postponed_1169_; lean_object* v_diag_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1179_; 
v___x_1161_ = lean_st_ref_get(v___y_1157_);
v_mctx_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc_ref(v_mctx_1162_);
lean_dec(v___x_1161_);
v___x_1163_ = l_Lean_instantiateMVarsCore(v_mctx_1162_, v_e_1156_);
v_fst_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_fst_1164_);
v_snd_1165_ = lean_ctor_get(v___x_1163_, 1);
lean_inc(v_snd_1165_);
lean_dec_ref(v___x_1163_);
v___x_1166_ = lean_st_ref_take(v___y_1157_);
v_cache_1167_ = lean_ctor_get(v___x_1166_, 1);
v_zetaDeltaFVarIds_1168_ = lean_ctor_get(v___x_1166_, 2);
v_postponed_1169_ = lean_ctor_get(v___x_1166_, 3);
v_diag_1170_ = lean_ctor_get(v___x_1166_, 4);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v___x_1166_, 0);
lean_dec(v_unused_1180_);
v___x_1172_ = v___x_1166_;
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_diag_1170_);
lean_inc(v_postponed_1169_);
lean_inc(v_zetaDeltaFVarIds_1168_);
lean_inc(v_cache_1167_);
lean_dec(v___x_1166_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1179_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v_snd_1165_);
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_snd_1165_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_cache_1167_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_zetaDeltaFVarIds_1168_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v_postponed_1169_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v_diag_1170_);
v___x_1175_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_st_ref_set(v___y_1157_, v___x_1175_);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v_fst_1164_);
return v___x_1177_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_e_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_e_1181_, v___y_1182_);
lean_dec(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_e_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_e_1185_, v___y_1189_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_e_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_e_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___lam__0(lean_object* v_k_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v_b_1206_, lean_object* v_c_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v___x_1213_; 
lean_inc(v___y_1211_);
lean_inc_ref(v___y_1210_);
lean_inc(v___y_1209_);
lean_inc_ref(v___y_1208_);
lean_inc(v___y_1205_);
lean_inc_ref(v___y_1204_);
v___x_1213_ = lean_apply_9(v_k_1203_, v_b_1206_, v_c_1207_, v___y_1204_, v___y_1205_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, lean_box(0));
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___lam__0___boxed(lean_object* v_k_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v_b_1217_, lean_object* v_c_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___lam__0(v_k_1214_, v___y_1215_, v___y_1216_, v_b_1217_, v_c_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_type_1225_, lean_object* v_k_1226_, uint8_t v_cleanupAnnotations_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___f_1235_; uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
v___f_1235_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1235_, 0, v_k_1226_);
lean_closure_set(v___f_1235_, 1, v___y_1228_);
lean_closure_set(v___f_1235_, 2, v___y_1229_);
v___x_1236_ = 0;
v___x_1237_ = lean_box(0);
v___x_1238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1236_, v___x_1237_, v_type_1225_, v___f_1235_, v_cleanupAnnotations_1227_, v___x_1236_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1238_) == 0)
{
return v___x_1238_;
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_type_1247_, lean_object* v_k_1248_, lean_object* v_cleanupAnnotations_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1257_; lean_object* v_res_1258_; 
v_cleanupAnnotations_boxed_1257_ = lean_unbox(v_cleanupAnnotations_1249_);
v_res_1258_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_type_1247_, v_k_1248_, v_cleanupAnnotations_boxed_1257_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_00_u03b1_1259_, lean_object* v_type_1260_, lean_object* v_k_1261_, uint8_t v_cleanupAnnotations_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_type_1260_, v_k_1261_, v_cleanupAnnotations_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_00_u03b1_1271_, lean_object* v_type_1272_, lean_object* v_k_1273_, lean_object* v_cleanupAnnotations_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1282_; lean_object* v_res_1283_; 
v_cleanupAnnotations_boxed_1282_ = lean_unbox(v_cleanupAnnotations_1274_);
v_res_1283_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_00_u03b1_1271_, v_type_1272_, v_k_1273_, v_cleanupAnnotations_boxed_1282_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_name_1284_, lean_object* v_levelParams_1285_, lean_object* v_type_1286_, lean_object* v_value_1287_, lean_object* v_hints_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v___x_1291_; uint8_t v___y_1293_; uint8_t v___y_1300_; lean_object* v_env_1303_; uint8_t v___x_1304_; 
v___x_1291_ = lean_st_ref_get(v___y_1289_);
v_env_1303_ = lean_ctor_get(v___x_1291_, 0);
lean_inc_ref(v_env_1303_);
lean_dec(v___x_1291_);
lean_inc_ref(v_env_1303_);
v___x_1304_ = l_Lean_Environment_hasUnsafe(v_env_1303_, v_type_1286_);
if (v___x_1304_ == 0)
{
uint8_t v___x_1305_; 
v___x_1305_ = l_Lean_Environment_hasUnsafe(v_env_1303_, v_value_1287_);
v___y_1300_ = v___x_1305_;
goto v___jp_1299_;
}
else
{
lean_dec_ref(v_env_1303_);
v___y_1300_ = v___x_1304_;
goto v___jp_1299_;
}
v___jp_1292_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_inc(v_name_1284_);
v___x_1294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1294_, 0, v_name_1284_);
lean_ctor_set(v___x_1294_, 1, v_levelParams_1285_);
lean_ctor_set(v___x_1294_, 2, v_type_1286_);
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1296_, 0, v_name_1284_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1297_, 0, v___x_1294_);
lean_ctor_set(v___x_1297_, 1, v_value_1287_);
lean_ctor_set(v___x_1297_, 2, v_hints_1288_);
lean_ctor_set(v___x_1297_, 3, v___x_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*4, v___y_1293_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
v___jp_1299_:
{
if (v___y_1300_ == 0)
{
uint8_t v___x_1301_; 
v___x_1301_ = 1;
v___y_1293_ = v___x_1301_;
goto v___jp_1292_;
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = 0;
v___y_1293_ = v___x_1302_;
goto v___jp_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_name_1306_, lean_object* v_levelParams_1307_, lean_object* v_type_1308_, lean_object* v_value_1309_, lean_object* v_hints_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_name_1306_, v_levelParams_1307_, v_type_1308_, v_value_1309_, v_hints_1310_, v___y_1311_);
lean_dec(v___y_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_name_1314_, lean_object* v_levelParams_1315_, lean_object* v_type_1316_, lean_object* v_value_1317_, lean_object* v_hints_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_name_1314_, v_levelParams_1315_, v_type_1316_, v_value_1317_, v_hints_1318_, v___y_1324_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_name_1327_, lean_object* v_levelParams_1328_, lean_object* v_type_1329_, lean_object* v_value_1330_, lean_object* v_hints_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_name_1327_, v_levelParams_1328_, v_type_1329_, v_value_1330_, v_hints_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg(lean_object* v_type_1340_, lean_object* v_maxFVars_x3f_1341_, lean_object* v_k_1342_, uint8_t v_cleanupAnnotations_1343_, uint8_t v_whnfType_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___f_1352_; lean_object* v___x_1353_; 
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
v___f_1352_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1352_, 0, v_k_1342_);
lean_closure_set(v___f_1352_, 1, v___y_1345_);
lean_closure_set(v___f_1352_, 2, v___y_1346_);
v___x_1353_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1340_, v_maxFVars_x3f_1341_, v___f_1352_, v_cleanupAnnotations_1343_, v_whnfType_1344_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
if (lean_obj_tag(v___x_1353_) == 0)
{
return v___x_1353_;
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg___boxed(lean_object* v_type_1362_, lean_object* v_maxFVars_x3f_1363_, lean_object* v_k_1364_, lean_object* v_cleanupAnnotations_1365_, lean_object* v_whnfType_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1374_; uint8_t v_whnfType_boxed_1375_; lean_object* v_res_1376_; 
v_cleanupAnnotations_boxed_1374_ = lean_unbox(v_cleanupAnnotations_1365_);
v_whnfType_boxed_1375_ = lean_unbox(v_whnfType_1366_);
v_res_1376_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg(v_type_1362_, v_maxFVars_x3f_1363_, v_k_1364_, v_cleanupAnnotations_boxed_1374_, v_whnfType_boxed_1375_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9(lean_object* v_00_u03b1_1377_, lean_object* v_type_1378_, lean_object* v_maxFVars_x3f_1379_, lean_object* v_k_1380_, uint8_t v_cleanupAnnotations_1381_, uint8_t v_whnfType_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg(v_type_1378_, v_maxFVars_x3f_1379_, v_k_1380_, v_cleanupAnnotations_1381_, v_whnfType_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___boxed(lean_object* v_00_u03b1_1391_, lean_object* v_type_1392_, lean_object* v_maxFVars_x3f_1393_, lean_object* v_k_1394_, lean_object* v_cleanupAnnotations_1395_, lean_object* v_whnfType_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1404_; uint8_t v_whnfType_boxed_1405_; lean_object* v_res_1406_; 
v_cleanupAnnotations_boxed_1404_ = lean_unbox(v_cleanupAnnotations_1395_);
v_whnfType_boxed_1405_ = lean_unbox(v_whnfType_1396_);
v_res_1406_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9(v_00_u03b1_1391_, v_type_1392_, v_maxFVars_x3f_1393_, v_k_1394_, v_cleanupAnnotations_boxed_1404_, v_whnfType_boxed_1405_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object* v_mvarId_1407_, lean_object* v_val_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v_mctx_1412_; lean_object* v_cache_1413_; lean_object* v_zetaDeltaFVarIds_1414_; lean_object* v_postponed_1415_; lean_object* v_diag_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1443_; 
v___x_1411_ = lean_st_ref_take(v___y_1409_);
v_mctx_1412_ = lean_ctor_get(v___x_1411_, 0);
v_cache_1413_ = lean_ctor_get(v___x_1411_, 1);
v_zetaDeltaFVarIds_1414_ = lean_ctor_get(v___x_1411_, 2);
v_postponed_1415_ = lean_ctor_get(v___x_1411_, 3);
v_diag_1416_ = lean_ctor_get(v___x_1411_, 4);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1418_ = v___x_1411_;
v_isShared_1419_ = v_isSharedCheck_1443_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_diag_1416_);
lean_inc(v_postponed_1415_);
lean_inc(v_zetaDeltaFVarIds_1414_);
lean_inc(v_cache_1413_);
lean_inc(v_mctx_1412_);
lean_dec(v___x_1411_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1443_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_depth_1420_; lean_object* v_levelAssignDepth_1421_; lean_object* v_mvarCounter_1422_; lean_object* v_lDepth_1423_; lean_object* v_decls_1424_; lean_object* v_userNames_1425_; lean_object* v_lAssignment_1426_; lean_object* v_eAssignment_1427_; lean_object* v_dAssignment_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1442_; 
v_depth_1420_ = lean_ctor_get(v_mctx_1412_, 0);
v_levelAssignDepth_1421_ = lean_ctor_get(v_mctx_1412_, 1);
v_mvarCounter_1422_ = lean_ctor_get(v_mctx_1412_, 2);
v_lDepth_1423_ = lean_ctor_get(v_mctx_1412_, 3);
v_decls_1424_ = lean_ctor_get(v_mctx_1412_, 4);
v_userNames_1425_ = lean_ctor_get(v_mctx_1412_, 5);
v_lAssignment_1426_ = lean_ctor_get(v_mctx_1412_, 6);
v_eAssignment_1427_ = lean_ctor_get(v_mctx_1412_, 7);
v_dAssignment_1428_ = lean_ctor_get(v_mctx_1412_, 8);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_mctx_1412_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1430_ = v_mctx_1412_;
v_isShared_1431_ = v_isSharedCheck_1442_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_dAssignment_1428_);
lean_inc(v_eAssignment_1427_);
lean_inc(v_lAssignment_1426_);
lean_inc(v_userNames_1425_);
lean_inc(v_decls_1424_);
lean_inc(v_lDepth_1423_);
lean_inc(v_mvarCounter_1422_);
lean_inc(v_levelAssignDepth_1421_);
lean_inc(v_depth_1420_);
lean_dec(v_mctx_1412_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1442_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1427_, v_mvarId_1407_, v_val_1408_);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 7, v___x_1432_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_depth_1420_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_levelAssignDepth_1421_);
lean_ctor_set(v_reuseFailAlloc_1441_, 2, v_mvarCounter_1422_);
lean_ctor_set(v_reuseFailAlloc_1441_, 3, v_lDepth_1423_);
lean_ctor_set(v_reuseFailAlloc_1441_, 4, v_decls_1424_);
lean_ctor_set(v_reuseFailAlloc_1441_, 5, v_userNames_1425_);
lean_ctor_set(v_reuseFailAlloc_1441_, 6, v_lAssignment_1426_);
lean_ctor_set(v_reuseFailAlloc_1441_, 7, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1441_, 8, v_dAssignment_1428_);
v___x_1434_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1434_);
v___x_1436_ = v___x_1418_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_cache_1413_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_zetaDeltaFVarIds_1414_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_postponed_1415_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_diag_1416_);
v___x_1436_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_st_ref_set(v___y_1409_, v___x_1436_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
return v___x_1439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_mvarId_1444_, lean_object* v_val_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_mvarId_1444_, v_val_1445_, v___y_1446_);
lean_dec(v___y_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_cls_1449_, lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_ref_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1502_; 
v_ref_1456_ = lean_ctor_get(v___y_1453_, 5);
v___x_1457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1502_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1502_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v_traceState_1463_; lean_object* v_env_1464_; lean_object* v_nextMacroScope_1465_; lean_object* v_ngen_1466_; lean_object* v_auxDeclNGen_1467_; lean_object* v_cache_1468_; lean_object* v_messages_1469_; lean_object* v_infoState_1470_; lean_object* v_snapshotTasks_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1501_; 
v___x_1462_ = lean_st_ref_take(v___y_1454_);
v_traceState_1463_ = lean_ctor_get(v___x_1462_, 4);
v_env_1464_ = lean_ctor_get(v___x_1462_, 0);
v_nextMacroScope_1465_ = lean_ctor_get(v___x_1462_, 1);
v_ngen_1466_ = lean_ctor_get(v___x_1462_, 2);
v_auxDeclNGen_1467_ = lean_ctor_get(v___x_1462_, 3);
v_cache_1468_ = lean_ctor_get(v___x_1462_, 5);
v_messages_1469_ = lean_ctor_get(v___x_1462_, 6);
v_infoState_1470_ = lean_ctor_get(v___x_1462_, 7);
v_snapshotTasks_1471_ = lean_ctor_get(v___x_1462_, 8);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1473_ = v___x_1462_;
v_isShared_1474_ = v_isSharedCheck_1501_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snapshotTasks_1471_);
lean_inc(v_infoState_1470_);
lean_inc(v_messages_1469_);
lean_inc(v_cache_1468_);
lean_inc(v_traceState_1463_);
lean_inc(v_auxDeclNGen_1467_);
lean_inc(v_ngen_1466_);
lean_inc(v_nextMacroScope_1465_);
lean_inc(v_env_1464_);
lean_dec(v___x_1462_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1501_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
uint64_t v_tid_1475_; lean_object* v_traces_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1500_; 
v_tid_1475_ = lean_ctor_get_uint64(v_traceState_1463_, sizeof(void*)*1);
v_traces_1476_ = lean_ctor_get(v_traceState_1463_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_traceState_1463_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1478_ = v_traceState_1463_;
v_isShared_1479_ = v_isSharedCheck_1500_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_traces_1476_);
lean_dec(v_traceState_1463_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1500_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; double v___x_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__0);
v___x_1482_ = 0;
v___x_1483_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1484_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1484_, 0, v_cls_1449_);
lean_ctor_set(v___x_1484_, 1, v___x_1480_);
lean_ctor_set(v___x_1484_, 2, v___x_1483_);
lean_ctor_set_float(v___x_1484_, sizeof(void*)*3, v___x_1481_);
lean_ctor_set_float(v___x_1484_, sizeof(void*)*3 + 8, v___x_1481_);
lean_ctor_set_uint8(v___x_1484_, sizeof(void*)*3 + 16, v___x_1482_);
v___x_1485_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__2));
v___x_1486_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v_a_1458_);
lean_ctor_set(v___x_1486_, 2, v___x_1485_);
lean_inc(v_ref_1456_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v_ref_1456_);
lean_ctor_set(v___x_1487_, 1, v___x_1486_);
v___x_1488_ = l_Lean_PersistentArray_push___redArg(v_traces_1476_, v___x_1487_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1488_);
v___x_1490_ = v___x_1478_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1488_);
lean_ctor_set_uint64(v_reuseFailAlloc_1499_, sizeof(void*)*1, v_tid_1475_);
v___x_1490_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v___x_1490_);
v___x_1492_ = v___x_1473_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_env_1464_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_nextMacroScope_1465_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_ngen_1466_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_auxDeclNGen_1467_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1498_, 5, v_cache_1468_);
lean_ctor_set(v_reuseFailAlloc_1498_, 6, v_messages_1469_);
lean_ctor_set(v_reuseFailAlloc_1498_, 7, v_infoState_1470_);
lean_ctor_set(v_reuseFailAlloc_1498_, 8, v_snapshotTasks_1471_);
v___x_1492_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1493_ = lean_st_ref_set(v___y_1454_, v___x_1492_);
v___x_1494_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1494_);
v___x_1496_ = v___x_1460_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1494_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_cls_1503_, lean_object* v_msg_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_cls_1503_, v_msg_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1510_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1511_; lean_object* v_dummy_1512_; 
v___x_1511_ = lean_box(0);
v_dummy_1512_ = l_Lean_Expr_sort___override(v___x_1511_);
return v_dummy_1512_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__1));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__3));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1519_, lean_object* v_numParams_1520_, lean_object* v___x_1521_, lean_object* v_name_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v_name_1525_, lean_object* v___x_1526_, lean_object* v_fields_1527_, lean_object* v_bodyExpr_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1629_; 
lean_inc(v_cls_1519_);
v___x_1536_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_cls_1519_, v___y_1533_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1629_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1629_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v_nargs_1541_; lean_object* v_dummy_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___y_1561_; uint8_t v___x_1612_; 
v_nargs_1541_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1528_);
v_dummy_1542_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0);
lean_inc(v_nargs_1541_);
v___x_1543_ = lean_mk_array(v_nargs_1541_, v_dummy_1542_);
v___x_1544_ = lean_unsigned_to_nat(1u);
v___x_1545_ = lean_nat_sub(v_nargs_1541_, v___x_1544_);
lean_dec(v_nargs_1541_);
v___x_1546_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1528_, v___x_1543_, v___x_1545_);
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
v___x_1612_ = lean_unbox(v_a_1537_);
lean_dec(v_a_1537_);
if (v___x_1612_ == 0)
{
lean_dec(v_cls_1519_);
v___y_1556_ = v___y_1529_;
v___y_1557_ = v___y_1530_;
v___y_1558_ = v___y_1531_;
v___y_1559_ = v___y_1532_;
v___y_1560_ = v___y_1533_;
v___y_1561_ = v___y_1534_;
goto v___jp_1555_;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1613_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__2);
lean_inc(v_name_1525_);
v___x_1614_ = l_Lean_MessageData_ofName(v_name_1525_);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__4);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
lean_inc_ref(v___x_1554_);
v___x_1618_ = l_Lean_MessageData_ofExpr(v___x_1554_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_cls_1519_, v___x_1619_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_dec_ref(v___x_1620_);
v___y_1556_ = v___y_1529_;
v___y_1557_ = v___y_1530_;
v___y_1558_ = v___y_1531_;
v___y_1559_ = v___y_1532_;
v___y_1560_ = v___y_1533_;
v___y_1561_ = v___y_1534_;
goto v___jp_1555_;
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec_ref(v___x_1554_);
lean_dec(v___x_1550_);
lean_del_object(v___x_1539_);
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
v___jp_1555_:
{
lean_object* v___x_1563_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v___x_1554_);
v___x_1563_ = v___x_1539_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1554_);
v___x_1563_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
uint8_t v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = 0;
v___x_1565_ = lean_box(0);
v___x_1566_ = l_Lean_Meta_mkFreshExprMVar(v___x_1563_, v___x_1564_, v___x_1565_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = l_Lean_Expr_mvarId_x21(v_a_1567_);
lean_inc(v___x_1568_);
v___x_1569_ = l_Lean_MVarId_getType(v___x_1568_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; uint8_t v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref(v___x_1569_);
v___x_1571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__1));
v___x_1572_ = l_Lean_Name_append(v___x_1550_, v___x_1571_);
lean_inc(v___x_1523_);
v___x_1573_ = l_Lean_mkConst(v___x_1572_, v___x_1523_);
v___x_1574_ = l_Lean_mkAppN(v___x_1573_, v___x_1524_);
v___x_1575_ = 0;
v___x_1576_ = 1;
v___x_1577_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1568_);
v___x_1578_ = l_Lean_MVarId_rewrite(v___x_1568_, v_a_1570_, v___x_1574_, v___x_1575_, v___x_1577_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v_eNew_1580_; lean_object* v_eqProof_1581_; lean_object* v___x_1582_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1578_);
v_eNew_1580_ = lean_ctor_get(v_a_1579_, 0);
lean_inc_ref(v_eNew_1580_);
v_eqProof_1581_ = lean_ctor_get(v_a_1579_, 1);
lean_inc_ref(v_eqProof_1581_);
lean_dec(v_a_1579_);
v___x_1582_ = l_Lean_MVarId_replaceTargetEq(v___x_1568_, v_eNew_1580_, v_eqProof_1581_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_a_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
v___x_1584_ = l_Lean_mkConst(v_name_1525_, v___x_1523_);
v___x_1585_ = l_Lean_mkAppN(v___x_1584_, v___x_1524_);
v___x_1586_ = l_Lean_mkAppN(v___x_1585_, v___x_1526_);
v___x_1587_ = l_Lean_mkAppN(v___x_1586_, v_fields_1527_);
v___x_1588_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1583_, v___x_1587_, v___y_1559_);
lean_dec_ref(v___x_1588_);
v___x_1589_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_a_1567_, v___y_1559_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___x_1591_ = 1;
v___x_1592_ = l_Lean_Meta_mkLambdaFVars(v_fields_1527_, v_a_1590_, v___x_1575_, v___x_1576_, v___x_1575_, v___x_1576_, v___x_1591_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1592_);
v___x_1594_ = l_Lean_Meta_mkLambdaFVars(v___x_1524_, v_a_1593_, v___x_1575_, v___x_1576_, v___x_1575_, v___x_1576_, v___x_1591_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v___x_1594_;
}
else
{
return v___x_1592_;
}
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_dec(v_a_1567_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
v_a_1595_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1582_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1582_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec(v___x_1568_);
lean_dec(v_a_1567_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
v_a_1603_ = lean_ctor_get(v___x_1578_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1578_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1578_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1578_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
else
{
lean_dec(v___x_1568_);
lean_dec(v_a_1567_);
lean_dec(v___x_1550_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
return v___x_1569_;
}
}
else
{
lean_dec(v___x_1550_);
lean_dec(v_name_1525_);
lean_dec(v___x_1523_);
return v___x_1566_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object** _args){
lean_object* v_cls_1630_ = _args[0];
lean_object* v_numParams_1631_ = _args[1];
lean_object* v___x_1632_ = _args[2];
lean_object* v_name_1633_ = _args[3];
lean_object* v___x_1634_ = _args[4];
lean_object* v___x_1635_ = _args[5];
lean_object* v_name_1636_ = _args[6];
lean_object* v___x_1637_ = _args[7];
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
v_res_1647_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1630_, v_numParams_1631_, v___x_1632_, v_name_1633_, v___x_1634_, v___x_1635_, v_name_1636_, v___x_1637_, v_fields_1638_, v_bodyExpr_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec_ref(v_fields_1638_);
lean_dec_ref(v___x_1637_);
lean_dec_ref(v___x_1635_);
lean_dec(v___x_1632_);
lean_dec(v_numParams_1631_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1648_, size_t v_sz_1649_, size_t v_i_1650_, lean_object* v_bs_1651_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1661_, lean_object* v_sz_1662_, lean_object* v_i_1663_, lean_object* v_bs_1664_){
_start:
{
size_t v_sz_boxed_1665_; size_t v_i_boxed_1666_; lean_object* v_res_1667_; 
v_sz_boxed_1665_ = lean_unbox_usize(v_sz_1662_);
lean_dec(v_sz_1662_);
v_i_boxed_1666_ = lean_unbox_usize(v_i_1663_);
lean_dec(v_i_1663_);
v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1661_, v_sz_boxed_1665_, v_i_boxed_1666_, v_bs_1664_);
lean_dec_ref(v___x_1661_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1668_, size_t v_sz_1669_, size_t v_i_1670_, lean_object* v_bs_1671_){
_start:
{
uint8_t v___x_1672_; 
v___x_1672_ = lean_usize_dec_lt(v_i_1670_, v_sz_1669_);
if (v___x_1672_ == 0)
{
lean_dec(v___x_1668_);
return v_bs_1671_;
}
else
{
lean_object* v_v_1673_; lean_object* v___x_1674_; lean_object* v_bs_x27_1675_; lean_object* v___x_1676_; size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v_v_1673_ = lean_array_uget(v_bs_1671_, v_i_1670_);
v___x_1674_ = lean_unsigned_to_nat(0u);
v_bs_x27_1675_ = lean_array_uset(v_bs_1671_, v_i_1670_, v___x_1674_);
lean_inc(v___x_1668_);
v___x_1676_ = l_Lean_mkConst(v_v_1673_, v___x_1668_);
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1670_, v___x_1677_);
v___x_1679_ = lean_array_uset(v_bs_x27_1675_, v_i_1670_, v___x_1676_);
v_i_1670_ = v___x_1678_;
v_bs_1671_ = v___x_1679_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1681_, lean_object* v_sz_1682_, lean_object* v_i_1683_, lean_object* v_bs_1684_){
_start:
{
size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1682_);
lean_dec(v_sz_1682_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1681_, v_sz_boxed_1685_, v_i_boxed_1686_, v_bs_1684_);
return v_res_1687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v___x_1691_, lean_object* v_numParams_1692_, lean_object* v___x_1693_, lean_object* v___x_1694_, size_t v___x_1695_, lean_object* v_cls_1696_, lean_object* v___x_1697_, lean_object* v_name_1698_, lean_object* v_name_1699_, lean_object* v_levelParams_1700_, lean_object* v_ctorSyntax_1701_, lean_object* v_args_1702_, lean_object* v_body_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; size_t v_sz_1714_; lean_object* v___x_1715_; size_t v_sz_1716_; lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; 
lean_inc(v_numParams_1692_);
v___x_1711_ = l_Array_extract___redArg(v_args_1702_, v___x_1691_, v_numParams_1692_);
v___x_1712_ = lean_array_get_size(v_args_1702_);
lean_inc(v_numParams_1692_);
v___x_1713_ = l_Array_toSubarray___redArg(v_args_1702_, v_numParams_1692_, v___x_1712_);
v_sz_1714_ = lean_array_size(v___x_1693_);
lean_inc(v___x_1694_);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1694_, v_sz_1714_, v___x_1695_, v___x_1693_);
v_sz_1716_ = lean_array_size(v___x_1715_);
v___x_1717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1711_, v_sz_1716_, v___x_1695_, v___x_1715_);
lean_inc_ref(v___x_1717_);
lean_inc(v_name_1699_);
lean_inc(v_cls_1696_);
v___f_1718_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed), 17, 8);
lean_closure_set(v___f_1718_, 0, v_cls_1696_);
lean_closure_set(v___f_1718_, 1, v_numParams_1692_);
lean_closure_set(v___f_1718_, 2, v___x_1697_);
lean_closure_set(v___f_1718_, 3, v_name_1698_);
lean_closure_set(v___f_1718_, 4, v___x_1694_);
lean_closure_set(v___f_1718_, 5, v___x_1711_);
lean_closure_set(v___f_1718_, 6, v_name_1699_);
lean_closure_set(v___f_1718_, 7, v___x_1717_);
v___x_1719_ = l_Subarray_copy___redArg(v___x_1713_);
v___x_1720_ = l_Lean_Expr_replaceFVars(v_body_1703_, v___x_1719_, v___x_1717_);
lean_dec_ref(v___x_1717_);
lean_dec_ref(v___x_1719_);
v___x_1721_ = 0;
v___x_1722_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1720_, v___f_1718_, v___x_1721_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref(v___x_1722_);
lean_inc(v___y_1709_);
lean_inc_ref(v___y_1708_);
lean_inc(v___y_1707_);
lean_inc_ref(v___y_1706_);
lean_inc(v_a_1723_);
v___x_1724_ = lean_infer_type(v_a_1723_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___y_1727_; lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___x_1749_; lean_object* v_a_1750_; uint8_t v___x_1751_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
lean_inc(v_cls_1696_);
v___x_1749_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_cls_1696_, v___y_1708_);
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
v___x_1751_ = lean_unbox(v_a_1750_);
lean_dec(v_a_1750_);
if (v___x_1751_ == 0)
{
lean_dec(v_cls_1696_);
v___y_1727_ = v___y_1704_;
v___y_1728_ = v___y_1705_;
v___y_1729_ = v___y_1706_;
v___y_1730_ = v___y_1707_;
v___y_1731_ = v___y_1708_;
v___y_1732_ = v___y_1709_;
goto v___jp_1726_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1752_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1);
lean_inc(v_a_1725_);
v___x_1753_ = l_Lean_MessageData_ofExpr(v_a_1725_);
v___x_1754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_cls_1696_, v___x_1754_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_dec_ref(v___x_1755_);
v___y_1727_ = v___y_1704_;
v___y_1728_ = v___y_1705_;
v___y_1729_ = v___y_1706_;
v___y_1730_ = v___y_1707_;
v___y_1731_ = v___y_1708_;
v___y_1732_ = v___y_1709_;
goto v___jp_1726_;
}
else
{
lean_dec(v_a_1725_);
lean_dec(v_a_1723_);
lean_dec(v_ctorSyntax_1701_);
lean_dec(v_levelParams_1700_);
lean_dec(v_name_1699_);
return v___x_1755_;
}
}
v___jp_1726_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1748_; 
v___x_1733_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1699_);
v___x_1734_ = lean_box(0);
lean_inc(v_a_1723_);
v___x_1735_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v___x_1733_, v_levelParams_1700_, v_a_1725_, v_a_1723_, v___x_1734_, v___y_1732_);
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1738_ = v___x_1735_;
v_isShared_1739_ = v_isSharedCheck_1748_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1735_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1748_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set_tag(v___x_1738_, 1);
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_addDecl(v___x_1741_, v___x_1721_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1742_) == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; 
lean_dec_ref(v___x_1742_);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_box(0);
v___x_1745_ = 1;
v___x_1746_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1701_, v_a_1723_, v___x_1743_, v___x_1743_, v___x_1744_, v___x_1745_, v___x_1721_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
return v___x_1746_;
}
else
{
lean_dec(v_a_1723_);
lean_dec(v_ctorSyntax_1701_);
return v___x_1742_;
}
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1723_);
lean_dec(v_ctorSyntax_1701_);
lean_dec(v_levelParams_1700_);
lean_dec(v_name_1699_);
lean_dec(v_cls_1696_);
v_a_1756_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1724_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1724_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec(v_ctorSyntax_1701_);
lean_dec(v_levelParams_1700_);
lean_dec(v_name_1699_);
lean_dec(v_cls_1696_);
v_a_1764_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1722_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1722_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v___x_1772_ = _args[0];
lean_object* v_numParams_1773_ = _args[1];
lean_object* v___x_1774_ = _args[2];
lean_object* v___x_1775_ = _args[3];
lean_object* v___x_1776_ = _args[4];
lean_object* v_cls_1777_ = _args[5];
lean_object* v___x_1778_ = _args[6];
lean_object* v_name_1779_ = _args[7];
lean_object* v_name_1780_ = _args[8];
lean_object* v_levelParams_1781_ = _args[9];
lean_object* v_ctorSyntax_1782_ = _args[10];
lean_object* v_args_1783_ = _args[11];
lean_object* v_body_1784_ = _args[12];
lean_object* v___y_1785_ = _args[13];
lean_object* v___y_1786_ = _args[14];
lean_object* v___y_1787_ = _args[15];
lean_object* v___y_1788_ = _args[16];
lean_object* v___y_1789_ = _args[17];
lean_object* v___y_1790_ = _args[18];
lean_object* v___y_1791_ = _args[19];
_start:
{
size_t v___x_8920__boxed_1792_; lean_object* v_res_1793_; 
v___x_8920__boxed_1792_ = lean_unbox_usize(v___x_1776_);
lean_dec(v___x_1776_);
v_res_1793_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v___x_1772_, v_numParams_1773_, v___x_1774_, v___x_1775_, v___x_8920__boxed_1792_, v_cls_1777_, v___x_1778_, v_name_1779_, v_name_1780_, v_levelParams_1781_, v_ctorSyntax_1782_, v_args_1783_, v_body_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec_ref(v_body_1784_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1794_, size_t v_i_1795_, lean_object* v_bs_1796_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = lean_usize_dec_lt(v_i_1795_, v_sz_1794_);
if (v___x_1797_ == 0)
{
return v_bs_1796_;
}
else
{
lean_object* v_v_1798_; lean_object* v_toConstantVal_1799_; lean_object* v_name_1800_; lean_object* v___x_1801_; lean_object* v_bs_x27_1802_; lean_object* v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v_v_1798_ = lean_array_uget_borrowed(v_bs_1796_, v_i_1795_);
v_toConstantVal_1799_ = lean_ctor_get(v_v_1798_, 0);
v_name_1800_ = lean_ctor_get(v_toConstantVal_1799_, 0);
lean_inc(v_name_1800_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v_bs_x27_1802_ = lean_array_uset(v_bs_1796_, v_i_1795_, v___x_1801_);
v___x_1803_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1800_);
v___x_1804_ = ((size_t)1ULL);
v___x_1805_ = lean_usize_add(v_i_1795_, v___x_1804_);
v___x_1806_ = lean_array_uset(v_bs_x27_1802_, v_i_1795_, v___x_1803_);
v_i_1795_ = v___x_1805_;
v_bs_1796_ = v___x_1806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1808_, lean_object* v_i_1809_, lean_object* v_bs_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1808_);
lean_dec(v_sz_1808_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1809_);
lean_dec(v_i_1809_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1811_, v_i_boxed_1812_, v_bs_1810_);
return v_res_1813_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1819_, lean_object* v_ctorSyntax_1820_, lean_object* v_numParams_1821_, lean_object* v_name_1822_, lean_object* v_ctor_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_cls_1831_; lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1875_; 
v_cls_1831_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_1832_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_cls_1831_, v_a_1828_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1875_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1875_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1875_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; uint8_t v___x_1867_; 
v___x_1837_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1867_ = lean_unbox(v_a_1833_);
lean_dec(v_a_1833_);
if (v___x_1867_ == 0)
{
v___y_1839_ = v_a_1824_;
v___y_1840_ = v_a_1825_;
v___y_1841_ = v_a_1826_;
v___y_1842_ = v_a_1827_;
v___y_1843_ = v_a_1828_;
v___y_1844_ = v_a_1829_;
goto v___jp_1838_;
}
else
{
lean_object* v_toConstantVal_1868_; lean_object* v_name_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_toConstantVal_1868_ = lean_ctor_get(v_ctor_1823_, 0);
v_name_1869_ = lean_ctor_get(v_toConstantVal_1868_, 0);
v___x_1870_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1);
lean_inc(v_name_1869_);
v___x_1871_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1869_);
v___x_1872_ = l_Lean_MessageData_ofName(v___x_1871_);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1870_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_cls_1831_, v___x_1873_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_dec_ref(v___x_1874_);
v___y_1839_ = v_a_1824_;
v___y_1840_ = v_a_1825_;
v___y_1841_ = v_a_1826_;
v___y_1842_ = v_a_1827_;
v___y_1843_ = v_a_1828_;
v___y_1844_ = v_a_1829_;
goto v___jp_1838_;
}
else
{
lean_del_object(v___x_1835_);
lean_dec_ref(v_ctor_1823_);
lean_dec(v_name_1822_);
lean_dec(v_numParams_1821_);
lean_dec(v_ctorSyntax_1820_);
lean_dec_ref(v_infos_1819_);
return v___x_1874_;
}
}
v___jp_1838_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_toConstantVal_1847_; lean_object* v_toConstantVal_1848_; lean_object* v_levelParams_1849_; lean_object* v_name_1850_; lean_object* v_levelParams_1851_; lean_object* v_type_1852_; lean_object* v___x_1853_; size_t v_sz_1854_; size_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___f_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = lean_array_get_borrowed(v___x_1837_, v_infos_1819_, v___x_1845_);
v_toConstantVal_1847_ = lean_ctor_get(v___x_1846_, 0);
v_toConstantVal_1848_ = lean_ctor_get(v_ctor_1823_, 0);
lean_inc_ref(v_toConstantVal_1848_);
lean_dec_ref(v_ctor_1823_);
v_levelParams_1849_ = lean_ctor_get(v_toConstantVal_1847_, 1);
lean_inc(v_levelParams_1849_);
v_name_1850_ = lean_ctor_get(v_toConstantVal_1848_, 0);
lean_inc(v_name_1850_);
v_levelParams_1851_ = lean_ctor_get(v_toConstantVal_1848_, 1);
lean_inc(v_levelParams_1851_);
v_type_1852_ = lean_ctor_get(v_toConstantVal_1848_, 2);
lean_inc_ref(v_type_1852_);
lean_dec_ref(v_toConstantVal_1848_);
v___x_1853_ = lean_array_get_size(v_infos_1819_);
v_sz_1854_ = lean_array_size(v_infos_1819_);
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1854_, v___x_1855_, v_infos_1819_);
v___x_1857_ = lean_box(0);
v___x_1858_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1849_, v___x_1857_);
v___x_1859_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1821_);
v___f_1860_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 20, 11);
lean_closure_set(v___f_1860_, 0, v___x_1845_);
lean_closure_set(v___f_1860_, 1, v_numParams_1821_);
lean_closure_set(v___f_1860_, 2, v___x_1856_);
lean_closure_set(v___f_1860_, 3, v___x_1858_);
lean_closure_set(v___f_1860_, 4, v___x_1859_);
lean_closure_set(v___f_1860_, 5, v_cls_1831_);
lean_closure_set(v___f_1860_, 6, v___x_1853_);
lean_closure_set(v___f_1860_, 7, v_name_1822_);
lean_closure_set(v___f_1860_, 8, v_name_1850_);
lean_closure_set(v___f_1860_, 9, v_levelParams_1851_);
lean_closure_set(v___f_1860_, 10, v_ctorSyntax_1820_);
v___x_1861_ = lean_nat_add(v_numParams_1821_, v___x_1853_);
lean_dec(v_numParams_1821_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 1);
lean_ctor_set(v___x_1835_, 0, v___x_1861_);
v___x_1863_ = v___x_1835_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
uint8_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = 0;
v___x_1865_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg(v_type_1852_, v___x_1863_, v___f_1860_, v___x_1864_, v___x_1864_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1876_, lean_object* v_ctorSyntax_1877_, lean_object* v_numParams_1878_, lean_object* v_name_1879_, lean_object* v_ctor_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
lean_object* v_res_1888_; 
v_res_1888_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1876_, v_ctorSyntax_1877_, v_numParams_1878_, v_name_1879_, v_ctor_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
return v_res_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_mvarId_1889_, lean_object* v_val_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_mvarId_1889_, v_val_1890_, v___y_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_mvarId_1899_, lean_object* v_val_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_mvarId_1899_, v_val_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_cls_1909_, lean_object* v_msg_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_cls_1909_, v_msg_1910_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_cls_1919_, lean_object* v_msg_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_cls_1919_, v_msg_1920_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
return v_res_1928_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_instMonadEIO(lean_box(0));
return v___x_1929_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v_toApplicative_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_2037_; 
v___x_1944_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1945_ = l_StateRefT_x27_instMonad___redArg(v___x_1944_);
v_toApplicative_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v___x_1945_, 1);
lean_dec(v_unused_2038_);
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_2037_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_toApplicative_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_2037_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v_toFunctor_1950_; lean_object* v_toSeq_1951_; lean_object* v_toSeqLeft_1952_; lean_object* v_toSeqRight_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_2035_; 
v_toFunctor_1950_ = lean_ctor_get(v_toApplicative_1946_, 0);
v_toSeq_1951_ = lean_ctor_get(v_toApplicative_1946_, 2);
v_toSeqLeft_1952_ = lean_ctor_get(v_toApplicative_1946_, 3);
v_toSeqRight_1953_ = lean_ctor_get(v_toApplicative_1946_, 4);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_toApplicative_1946_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v_toApplicative_1946_, 1);
lean_dec(v_unused_2036_);
v___x_1955_ = v_toApplicative_1946_;
v_isShared_1956_ = v_isSharedCheck_2035_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_toSeqRight_1953_);
lean_inc(v_toSeqLeft_1952_);
lean_inc(v_toSeq_1951_);
lean_inc(v_toFunctor_1950_);
lean_dec(v_toApplicative_1946_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_2035_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___f_1957_; lean_object* v___f_1958_; lean_object* v___f_1959_; lean_object* v___f_1960_; lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___f_1963_; lean_object* v___f_1964_; lean_object* v___x_1966_; 
v___f_1957_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1958_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1950_);
v___f_1959_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1959_, 0, v_toFunctor_1950_);
v___f_1960_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1960_, 0, v_toFunctor_1950_);
v___x_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___f_1959_);
lean_ctor_set(v___x_1961_, 1, v___f_1960_);
v___f_1962_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1962_, 0, v_toSeqRight_1953_);
v___f_1963_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1963_, 0, v_toSeqLeft_1952_);
v___f_1964_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1964_, 0, v_toSeq_1951_);
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 4, v___f_1962_);
lean_ctor_set(v___x_1955_, 3, v___f_1963_);
lean_ctor_set(v___x_1955_, 2, v___f_1964_);
lean_ctor_set(v___x_1955_, 1, v___f_1957_);
lean_ctor_set(v___x_1955_, 0, v___x_1961_);
v___x_1966_ = v___x_1955_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___f_1957_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v___f_1964_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v___f_1963_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v___f_1962_);
v___x_1966_ = v_reuseFailAlloc_2034_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
lean_object* v___x_1968_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 1, v___f_1958_);
lean_ctor_set(v___x_1948_, 0, v___x_1966_);
v___x_1968_ = v___x_1948_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___f_1958_);
v___x_1968_ = v_reuseFailAlloc_2033_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v_toApplicative_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2031_; 
v___x_1969_ = l_StateRefT_x27_instMonad___redArg(v___x_1968_);
v_toApplicative_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_2031_ == 0)
{
lean_object* v_unused_2032_; 
v_unused_2032_ = lean_ctor_get(v___x_1969_, 1);
lean_dec(v_unused_2032_);
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_2031_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_toApplicative_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2031_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_toFunctor_1974_; lean_object* v_toSeq_1975_; lean_object* v_toSeqLeft_1976_; lean_object* v_toSeqRight_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2029_; 
v_toFunctor_1974_ = lean_ctor_get(v_toApplicative_1970_, 0);
v_toSeq_1975_ = lean_ctor_get(v_toApplicative_1970_, 2);
v_toSeqLeft_1976_ = lean_ctor_get(v_toApplicative_1970_, 3);
v_toSeqRight_1977_ = lean_ctor_get(v_toApplicative_1970_, 4);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_toApplicative_1970_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_toApplicative_1970_, 1);
lean_dec(v_unused_2030_);
v___x_1979_ = v_toApplicative_1970_;
v_isShared_1980_ = v_isSharedCheck_2029_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_toSeqRight_1977_);
lean_inc(v_toSeqLeft_1976_);
lean_inc(v_toSeq_1975_);
lean_inc(v_toFunctor_1974_);
lean_dec(v_toApplicative_1970_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2029_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___f_1981_; lean_object* v___f_1982_; lean_object* v___f_1983_; lean_object* v___f_1984_; lean_object* v___x_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1990_; 
v___f_1981_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1982_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1974_);
v___f_1983_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1983_, 0, v_toFunctor_1974_);
v___f_1984_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1984_, 0, v_toFunctor_1974_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___f_1983_);
lean_ctor_set(v___x_1985_, 1, v___f_1984_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toSeqRight_1977_);
v___f_1987_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1987_, 0, v_toSeqLeft_1976_);
v___f_1988_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1988_, 0, v_toSeq_1975_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v___f_1986_);
lean_ctor_set(v___x_1979_, 3, v___f_1987_);
lean_ctor_set(v___x_1979_, 2, v___f_1988_);
lean_ctor_set(v___x_1979_, 1, v___f_1981_);
lean_ctor_set(v___x_1979_, 0, v___x_1985_);
v___x_1990_ = v___x_1979_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___f_1981_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v___f_1988_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v___f_1987_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v___f_1986_);
v___x_1990_ = v_reuseFailAlloc_2028_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v___x_1992_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v___f_1982_);
lean_ctor_set(v___x_1972_, 0, v___x_1990_);
v___x_1992_ = v___x_1972_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___f_1982_);
v___x_1992_ = v_reuseFailAlloc_2027_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v_toApplicative_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2025_; 
v___x_1993_ = l_StateRefT_x27_instMonad___redArg(v___x_1992_);
v_toApplicative_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_1993_, 1);
lean_dec(v_unused_2026_);
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2025_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_toApplicative_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2025_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_toFunctor_1998_; lean_object* v_toSeq_1999_; lean_object* v_toSeqLeft_2000_; lean_object* v_toSeqRight_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2023_; 
v_toFunctor_1998_ = lean_ctor_get(v_toApplicative_1994_, 0);
v_toSeq_1999_ = lean_ctor_get(v_toApplicative_1994_, 2);
v_toSeqLeft_2000_ = lean_ctor_get(v_toApplicative_1994_, 3);
v_toSeqRight_2001_ = lean_ctor_get(v_toApplicative_1994_, 4);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_toApplicative_1994_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v_toApplicative_1994_, 1);
lean_dec(v_unused_2024_);
v___x_2003_ = v_toApplicative_1994_;
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_toSeqRight_2001_);
lean_inc(v_toSeqLeft_2000_);
lean_inc(v_toSeq_1999_);
lean_inc(v_toFunctor_1998_);
lean_dec(v_toApplicative_1994_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___f_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; lean_object* v___f_2010_; lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___x_2014_; 
v___f_2005_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_2006_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1998_);
v___f_2007_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2007_, 0, v_toFunctor_1998_);
v___f_2008_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2008_, 0, v_toFunctor_1998_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___f_2007_);
lean_ctor_set(v___x_2009_, 1, v___f_2008_);
v___f_2010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2010_, 0, v_toSeqRight_2001_);
v___f_2011_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2011_, 0, v_toSeqLeft_2000_);
v___f_2012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2012_, 0, v_toSeq_1999_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v___f_2010_);
lean_ctor_set(v___x_2003_, 3, v___f_2011_);
lean_ctor_set(v___x_2003_, 2, v___f_2012_);
lean_ctor_set(v___x_2003_, 1, v___f_2005_);
lean_ctor_set(v___x_2003_, 0, v___x_2009_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___f_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v___f_2012_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v___f_2011_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v___f_2010_);
v___x_2014_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___f_2006_);
lean_ctor_set(v___x_1996_, 0, v___x_2014_);
v___x_2016_ = v___x_1996_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___f_2006_);
v___x_2016_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_3780__overap_2019_; lean_object* v___x_2020_; 
v___x_2017_ = lean_box(0);
v___x_2018_ = l_instInhabitedOfMonad___redArg(v___x_2016_, v___x_2017_);
v___x_3780__overap_2019_ = lean_panic_fn(v___x_2018_, v_msg_1936_);
lean_inc(v___y_1942_);
lean_inc_ref(v___y_1941_);
lean_inc(v___y_1940_);
lean_inc_ref(v___y_1939_);
lean_inc(v___y_1938_);
lean_inc_ref(v___y_1937_);
v___x_2020_ = lean_apply_7(v___x_3780__overap_2019_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, lean_box(0));
return v___x_2020_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2047_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2048_, lean_object* v_opt_2049_){
_start:
{
lean_object* v_name_2050_; lean_object* v_defValue_2051_; lean_object* v_map_2052_; lean_object* v___x_2053_; 
v_name_2050_ = lean_ctor_get(v_opt_2049_, 0);
v_defValue_2051_ = lean_ctor_get(v_opt_2049_, 1);
v_map_2052_ = lean_ctor_get(v_opts_2048_, 0);
v___x_2053_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2052_, v_name_2050_);
if (lean_obj_tag(v___x_2053_) == 0)
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_unbox(v_defValue_2051_);
return v___x_2054_;
}
else
{
lean_object* v_val_2055_; 
v_val_2055_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_val_2055_);
lean_dec_ref(v___x_2053_);
if (lean_obj_tag(v_val_2055_) == 1)
{
uint8_t v_v_2056_; 
v_v_2056_ = lean_ctor_get_uint8(v_val_2055_, 0);
lean_dec_ref(v_val_2055_);
return v_v_2056_;
}
else
{
uint8_t v___x_2057_; 
lean_dec(v_val_2055_);
v___x_2057_ = lean_unbox(v_defValue_2051_);
return v___x_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2058_, lean_object* v_opt_2059_){
_start:
{
uint8_t v_res_2060_; lean_object* v_r_2061_; 
v_res_2060_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2058_, v_opt_2059_);
lean_dec_ref(v_opt_2059_);
lean_dec_ref(v_opts_2058_);
v_r_2061_ = lean_box(v_res_2060_);
return v_r_2061_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
v___x_2062_ = lean_box(1);
v___x_2063_ = l_Lean_MessageData_ofFormat(v___x_2062_);
return v___x_2063_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2068_ = l_Lean_MessageData_ofFormat(v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
if (lean_obj_tag(v_x_2070_) == 0)
{
return v_x_2069_;
}
else
{
lean_object* v_head_2071_; lean_object* v_tail_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2094_; 
v_head_2071_ = lean_ctor_get(v_x_2070_, 0);
v_tail_2072_ = lean_ctor_get(v_x_2070_, 1);
v_isSharedCheck_2094_ = !lean_is_exclusive(v_x_2070_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2074_ = v_x_2070_;
v_isShared_2075_ = v_isSharedCheck_2094_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_tail_2072_);
lean_inc(v_head_2071_);
lean_dec(v_x_2070_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2094_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v_before_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2092_; 
v_before_2076_ = lean_ctor_get(v_head_2071_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_head_2071_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v_head_2071_, 1);
lean_dec(v_unused_2093_);
v___x_2078_ = v_head_2071_;
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_before_2076_);
lean_dec(v_head_2071_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2092_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set_tag(v___x_2078_, 7);
lean_ctor_set(v___x_2078_, 1, v___x_2080_);
lean_ctor_set(v___x_2078_, 0, v_x_2069_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v_x_2069_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2083_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2075_ == 0)
{
lean_ctor_set_tag(v___x_2074_, 7);
lean_ctor_set(v___x_2074_, 1, v___x_2083_);
lean_ctor_set(v___x_2074_, 0, v___x_2082_);
v___x_2085_ = v___x_2074_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = l_Lean_MessageData_ofSyntax(v_before_2076_);
v___x_2087_ = l_Lean_indentD(v___x_2086_);
v___x_2088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2085_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
v_x_2069_ = v___x_2088_;
v_x_2070_ = v_tail_2072_;
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
lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2099_ = l_Lean_MessageData_ofFormat(v___x_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2100_, lean_object* v_macroStack_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_options_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_options_2104_ = lean_ctor_get(v___y_2102_, 2);
v___x_2105_ = l_Lean_Elab_pp_macroStack;
v___x_2106_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_options_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; 
lean_dec(v_macroStack_2101_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v_msgData_2100_);
return v___x_2107_;
}
else
{
if (lean_obj_tag(v_macroStack_2101_) == 0)
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2108_, 0, v_msgData_2100_);
return v___x_2108_;
}
else
{
lean_object* v_head_2109_; lean_object* v_after_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2125_; 
v_head_2109_ = lean_ctor_get(v_macroStack_2101_, 0);
lean_inc(v_head_2109_);
v_after_2110_ = lean_ctor_get(v_head_2109_, 1);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_head_2109_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v_head_2109_, 0);
lean_dec(v_unused_2126_);
v___x_2112_ = v_head_2109_;
v_isShared_2113_ = v_isSharedCheck_2125_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_after_2110_);
lean_dec(v_head_2109_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2125_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2113_ == 0)
{
lean_ctor_set_tag(v___x_2112_, 7);
lean_ctor_set(v___x_2112_, 1, v___x_2114_);
lean_ctor_set(v___x_2112_, 0, v_msgData_2100_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_msgData_2100_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v_msgData_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2117_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = l_Lean_MessageData_ofSyntax(v_after_2110_);
v___x_2120_ = l_Lean_indentD(v___x_2119_);
v_msgData_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2121_, 0, v___x_2118_);
lean_ctor_set(v_msgData_2121_, 1, v___x_2120_);
v___x_2122_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2121_, v_macroStack_2101_);
v___x_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
return v___x_2123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2127_, lean_object* v_macroStack_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2127_, v_macroStack_2128_, v___y_2129_);
lean_dec_ref(v___y_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_ref_2140_; lean_object* v___x_2141_; lean_object* v_a_2142_; lean_object* v_macroStack_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2154_; 
v_ref_2140_ = lean_ctor_get(v___y_2137_, 5);
v___x_2141_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2132_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_);
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2141_);
v_macroStack_2143_ = lean_ctor_get(v___y_2133_, 1);
lean_inc(v_macroStack_2143_);
lean_dec_ref(v___y_2133_);
lean_inc(v_macroStack_2143_);
v___x_2144_ = l_Lean_Elab_getBetterRef(v_ref_2140_, v_macroStack_2143_);
v___x_2145_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2142_, v_macroStack_2143_, v___y_2137_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2154_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2144_);
lean_ctor_set(v___x_2150_, 1, v_a_2146_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set_tag(v___x_2148_, 1);
lean_ctor_set(v___x_2148_, 0, v___x_2150_);
v___x_2152_ = v___x_2148_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
return v_res_2163_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2166_ = l_Lean_stringToMessageData(v___x_2165_);
return v___x_2166_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2168_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2169_ = l_Lean_stringToMessageData(v___x_2168_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2173_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2174_ = lean_unsigned_to_nat(11u);
v___x_2175_ = lean_unsigned_to_nat(122u);
v___x_2176_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2177_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2178_ = l_mkPanicMessageWithDecl(v___x_2177_, v___x_2176_, v___x_2175_, v___x_2174_, v___x_2173_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2195_; lean_object* v_env_2196_; uint8_t v___x_2197_; lean_object* v___x_2198_; 
v___x_2195_ = lean_st_ref_get(v___y_2185_);
v_env_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc_ref(v_env_2196_);
lean_dec(v___x_2195_);
v___x_2197_ = 0;
lean_inc(v_constName_2179_);
v___x_2198_ = l_Lean_Environment_findAsync_x3f(v_env_2196_, v_constName_2179_, v___x_2197_);
if (lean_obj_tag(v___x_2198_) == 1)
{
lean_object* v_val_2199_; uint8_t v_kind_2200_; 
v_val_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_val_2199_);
lean_dec_ref(v___x_2198_);
v_kind_2200_ = lean_ctor_get_uint8(v_val_2199_, sizeof(void*)*3);
if (v_kind_2200_ == 6)
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2199_);
if (lean_obj_tag(v___x_2201_) == 6)
{
lean_object* v_val_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec(v_constName_2179_);
v_val_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_val_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set_tag(v___x_2204_, 0);
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_val_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_dec_ref(v___x_2201_);
v___x_2210_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2211_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2210_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2220_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2220_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2220_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
if (lean_obj_tag(v_a_2212_) == 0)
{
lean_del_object(v___x_2214_);
goto v___jp_2187_;
}
else
{
lean_object* v_val_2216_; lean_object* v___x_2218_; 
lean_dec(v_constName_2179_);
v_val_2216_ = lean_ctor_get(v_a_2212_, 0);
lean_inc(v_val_2216_);
lean_dec_ref(v_a_2212_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v_val_2216_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_val_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec(v_constName_2179_);
v_a_2221_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2211_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2211_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
else
{
lean_dec(v_val_2199_);
goto v___jp_2187_;
}
}
else
{
lean_dec(v___x_2198_);
goto v___jp_2187_;
}
v___jp_2187_:
{
lean_object* v___x_2188_; uint8_t v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2188_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2189_ = 0;
v___x_2190_ = l_Lean_MessageData_ofConstName(v_constName_2179_, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2188_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
lean_inc_ref(v___y_2180_);
v___x_2194_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2193_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2238_, lean_object* v_infos_2239_, lean_object* v_numParams_2240_, lean_object* v_as_x27_2241_, lean_object* v_b_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
if (lean_obj_tag(v_as_x27_2241_) == 0)
{
lean_object* v___x_2250_; 
lean_dec(v_numParams_2240_);
lean_dec_ref(v_infos_2239_);
lean_dec_ref(v_a_2238_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v_b_2242_);
return v___x_2250_;
}
else
{
lean_object* v_head_2251_; lean_object* v_tail_2252_; lean_object* v_array_2253_; lean_object* v_start_2254_; lean_object* v_stop_2255_; uint8_t v___x_2256_; 
v_head_2251_ = lean_ctor_get(v_as_x27_2241_, 0);
lean_inc(v_head_2251_);
v_tail_2252_ = lean_ctor_get(v_as_x27_2241_, 1);
lean_inc(v_tail_2252_);
lean_dec_ref(v_as_x27_2241_);
v_array_2253_ = lean_ctor_get(v_b_2242_, 0);
v_start_2254_ = lean_ctor_get(v_b_2242_, 1);
v_stop_2255_ = lean_ctor_get(v_b_2242_, 2);
v___x_2256_ = lean_nat_dec_lt(v_start_2254_, v_stop_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; 
lean_dec(v_tail_2252_);
lean_dec(v_head_2251_);
lean_dec(v_numParams_2240_);
lean_dec_ref(v_infos_2239_);
lean_dec_ref(v_a_2238_);
v___x_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2257_, 0, v_b_2242_);
return v___x_2257_;
}
else
{
lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2289_; 
lean_inc(v_stop_2255_);
lean_inc(v_start_2254_);
lean_inc_ref(v_array_2253_);
v_isSharedCheck_2289_ = !lean_is_exclusive(v_b_2242_);
if (v_isSharedCheck_2289_ == 0)
{
lean_object* v_unused_2290_; lean_object* v_unused_2291_; lean_object* v_unused_2292_; 
v_unused_2290_ = lean_ctor_get(v_b_2242_, 2);
lean_dec(v_unused_2290_);
v_unused_2291_ = lean_ctor_get(v_b_2242_, 1);
lean_dec(v_unused_2291_);
v_unused_2292_ = lean_ctor_get(v_b_2242_, 0);
lean_dec(v_unused_2292_);
v___x_2259_ = v_b_2242_;
v_isShared_2260_ = v_isSharedCheck_2289_;
goto v_resetjp_2258_;
}
else
{
lean_dec(v_b_2242_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2289_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2251_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_toConstantVal_2262_; lean_object* v_a_2263_; lean_object* v_name_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_toConstantVal_2262_ = lean_ctor_get(v_a_2238_, 0);
v_a_2263_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2261_);
v_name_2264_ = lean_ctor_get(v_toConstantVal_2262_, 0);
v___x_2265_ = lean_array_fget_borrowed(v_array_2253_, v_start_2254_);
lean_inc(v_name_2264_);
lean_inc(v_numParams_2240_);
lean_inc(v___x_2265_);
lean_inc_ref(v_infos_2239_);
v___x_2266_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2239_, v___x_2265_, v_numParams_2240_, v_name_2264_, v_a_2263_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
lean_dec_ref(v___x_2266_);
v___x_2267_ = lean_unsigned_to_nat(1u);
v___x_2268_ = lean_nat_add(v_start_2254_, v___x_2267_);
lean_dec(v_start_2254_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2268_);
v___x_2270_ = v___x_2259_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_array_2253_);
lean_ctor_set(v_reuseFailAlloc_2272_, 1, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2272_, 2, v_stop_2255_);
v___x_2270_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
v_as_x27_2241_ = v_tail_2252_;
v_b_2242_ = v___x_2270_;
goto _start;
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_del_object(v___x_2259_);
lean_dec(v_stop_2255_);
lean_dec(v_start_2254_);
lean_dec_ref(v_array_2253_);
lean_dec(v_tail_2252_);
lean_dec(v_numParams_2240_);
lean_dec_ref(v_infos_2239_);
lean_dec_ref(v_a_2238_);
v_a_2273_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2266_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2266_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_del_object(v___x_2259_);
lean_dec(v_stop_2255_);
lean_dec(v_start_2254_);
lean_dec_ref(v_array_2253_);
lean_dec(v_tail_2252_);
lean_dec(v_numParams_2240_);
lean_dec_ref(v_infos_2239_);
lean_dec_ref(v_a_2238_);
v_a_2281_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2261_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2261_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2293_, lean_object* v_infos_2294_, lean_object* v_numParams_2295_, lean_object* v_as_x27_2296_, lean_object* v_b_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2293_, v_infos_2294_, v_numParams_2295_, v_as_x27_2296_, v_b_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2306_, lean_object* v_numParams_2307_, lean_object* v_as_2308_, size_t v_sz_2309_, size_t v_i_2310_, lean_object* v_b_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_lt(v_i_2310_, v_sz_2309_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
lean_dec(v_numParams_2307_);
lean_dec_ref(v_infos_2306_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_b_2311_);
return v___x_2320_;
}
else
{
lean_object* v_array_2321_; lean_object* v_start_2322_; lean_object* v_stop_2323_; uint8_t v___x_2324_; 
v_array_2321_ = lean_ctor_get(v_b_2311_, 0);
v_start_2322_ = lean_ctor_get(v_b_2311_, 1);
v_stop_2323_ = lean_ctor_get(v_b_2311_, 2);
v___x_2324_ = lean_nat_dec_lt(v_start_2322_, v_stop_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; 
lean_dec(v_numParams_2307_);
lean_dec_ref(v_infos_2306_);
v___x_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2325_, 0, v_b_2311_);
return v___x_2325_;
}
else
{
lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2353_; 
lean_inc(v_stop_2323_);
lean_inc(v_start_2322_);
lean_inc_ref(v_array_2321_);
v_isSharedCheck_2353_ = !lean_is_exclusive(v_b_2311_);
if (v_isSharedCheck_2353_ == 0)
{
lean_object* v_unused_2354_; lean_object* v_unused_2355_; lean_object* v_unused_2356_; 
v_unused_2354_ = lean_ctor_get(v_b_2311_, 2);
lean_dec(v_unused_2354_);
v_unused_2355_ = lean_ctor_get(v_b_2311_, 1);
lean_dec(v_unused_2355_);
v_unused_2356_ = lean_ctor_get(v_b_2311_, 0);
lean_dec(v_unused_2356_);
v___x_2327_ = v_b_2311_;
v_isShared_2328_ = v_isSharedCheck_2353_;
goto v_resetjp_2326_;
}
else
{
lean_dec(v_b_2311_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2353_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2329_; lean_object* v_ctorSyntax_2330_; lean_object* v_a_2331_; lean_object* v_ctors_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2329_ = lean_array_fget_borrowed(v_array_2321_, v_start_2322_);
v_ctorSyntax_2330_ = lean_ctor_get(v___x_2329_, 4);
v_a_2331_ = lean_array_uget_borrowed(v_as_2308_, v_i_2310_);
v_ctors_2332_ = lean_ctor_get(v_a_2331_, 4);
v___x_2333_ = lean_array_get_size(v_ctorSyntax_2330_);
v___x_2334_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ctorSyntax_2330_);
v___x_2335_ = l_Array_toSubarray___redArg(v_ctorSyntax_2330_, v___x_2334_, v___x_2333_);
lean_inc(v_ctors_2332_);
lean_inc(v_numParams_2307_);
lean_inc_ref(v_infos_2306_);
lean_inc(v_a_2331_);
v___x_2336_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2331_, v_infos_2306_, v_numParams_2307_, v_ctors_2332_, v___x_2335_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
lean_dec_ref(v___x_2336_);
v___x_2337_ = lean_unsigned_to_nat(1u);
v___x_2338_ = lean_nat_add(v_start_2322_, v___x_2337_);
lean_dec(v_start_2322_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 1, v___x_2338_);
v___x_2340_ = v___x_2327_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_array_2321_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2344_, 2, v_stop_2323_);
v___x_2340_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
size_t v___x_2341_; size_t v___x_2342_; 
v___x_2341_ = ((size_t)1ULL);
v___x_2342_ = lean_usize_add(v_i_2310_, v___x_2341_);
v_i_2310_ = v___x_2342_;
v_b_2311_ = v___x_2340_;
goto _start;
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_del_object(v___x_2327_);
lean_dec(v_stop_2323_);
lean_dec(v_start_2322_);
lean_dec_ref(v_array_2321_);
lean_dec(v_numParams_2307_);
lean_dec_ref(v_infos_2306_);
v_a_2345_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2336_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2336_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2357_, lean_object* v_numParams_2358_, lean_object* v_as_2359_, lean_object* v_sz_2360_, lean_object* v_i_2361_, lean_object* v_b_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
size_t v_sz_boxed_2370_; size_t v_i_boxed_2371_; lean_object* v_res_2372_; 
v_sz_boxed_2370_ = lean_unbox_usize(v_sz_2360_);
lean_dec(v_sz_2360_);
v_i_boxed_2371_ = lean_unbox_usize(v_i_2361_);
lean_dec(v_i_2361_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2357_, v_numParams_2358_, v_as_2359_, v_sz_boxed_2370_, v_i_boxed_2371_, v_b_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec_ref(v_as_2359_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2373_, lean_object* v_infos_2374_, lean_object* v_coinductiveElabData_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; size_t v_sz_2386_; size_t v___x_2387_; lean_object* v___x_2388_; 
v___x_2383_ = lean_unsigned_to_nat(0u);
v___x_2384_ = lean_array_get_size(v_coinductiveElabData_2375_);
v___x_2385_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2375_, v___x_2383_, v___x_2384_);
v_sz_2386_ = lean_array_size(v_infos_2374_);
v___x_2387_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2374_);
v___x_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2374_, v_numParams_2373_, v_infos_2374_, v_sz_2386_, v___x_2387_, v___x_2385_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec_ref(v_infos_2374_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2396_; 
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v___x_2388_, 0);
lean_dec(v_unused_2397_);
v___x_2390_ = v___x_2388_;
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
else
{
lean_dec(v___x_2388_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_box(0);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2392_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
else
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2405_; 
v_a_2398_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2400_ = v___x_2388_;
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2388_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2405_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_a_2398_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2406_, lean_object* v_infos_2407_, lean_object* v_coinductiveElabData_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2406_, v_infos_2407_, v_coinductiveElabData_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_);
lean_dec(v_a_2414_);
lean_dec_ref(v_a_2413_);
lean_dec(v_a_2412_);
lean_dec_ref(v_a_2411_);
lean_dec(v_a_2410_);
lean_dec_ref(v_a_2409_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2417_, lean_object* v_infos_2418_, lean_object* v_numParams_2419_, lean_object* v_as_2420_, lean_object* v_as_x27_2421_, lean_object* v_b_2422_, lean_object* v_a_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2417_, v_infos_2418_, v_numParams_2419_, v_as_x27_2421_, v_b_2422_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2432_, lean_object* v_infos_2433_, lean_object* v_numParams_2434_, lean_object* v_as_2435_, lean_object* v_as_x27_2436_, lean_object* v_b_2437_, lean_object* v_a_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2432_, v_infos_2433_, v_numParams_2434_, v_as_2435_, v_as_x27_2436_, v_b_2437_, v_a_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v_as_2435_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2447_, lean_object* v_msg_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; 
lean_inc_ref(v___y_2449_);
v___x_2456_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2457_, lean_object* v_msg_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2457_, v_msg_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2467_, lean_object* v_macroStack_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2467_, v_macroStack_2468_, v___y_2473_);
return v___x_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2477_, lean_object* v_macroStack_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2477_, v_macroStack_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_type_2487_, lean_object* v_maxFVars_x3f_2488_, lean_object* v_k_2489_, uint8_t v_cleanupAnnotations_2490_, uint8_t v_whnfType_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___f_2497_; lean_object* v___x_2498_; 
v___f_2497_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2497_, 0, v_k_2489_);
v___x_2498_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2487_, v_maxFVars_x3f_2488_, v___f_2497_, v_cleanupAnnotations_2490_, v_whnfType_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2498_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2498_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
v_a_2507_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2498_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2498_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_type_2515_, lean_object* v_maxFVars_x3f_2516_, lean_object* v_k_2517_, lean_object* v_cleanupAnnotations_2518_, lean_object* v_whnfType_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2525_; uint8_t v_whnfType_boxed_2526_; lean_object* v_res_2527_; 
v_cleanupAnnotations_boxed_2525_ = lean_unbox(v_cleanupAnnotations_2518_);
v_whnfType_boxed_2526_ = lean_unbox(v_whnfType_2519_);
v_res_2527_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_type_2515_, v_maxFVars_x3f_2516_, v_k_2517_, v_cleanupAnnotations_boxed_2525_, v_whnfType_boxed_2526_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2528_, lean_object* v_type_2529_, lean_object* v_maxFVars_x3f_2530_, lean_object* v_k_2531_, uint8_t v_cleanupAnnotations_2532_, uint8_t v_whnfType_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v___x_2539_; 
v___x_2539_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_type_2529_, v_maxFVars_x3f_2530_, v_k_2531_, v_cleanupAnnotations_2532_, v_whnfType_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2540_, lean_object* v_type_2541_, lean_object* v_maxFVars_x3f_2542_, lean_object* v_k_2543_, lean_object* v_cleanupAnnotations_2544_, lean_object* v_whnfType_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2551_; uint8_t v_whnfType_boxed_2552_; lean_object* v_res_2553_; 
v_cleanupAnnotations_boxed_2551_ = lean_unbox(v_cleanupAnnotations_2544_);
v_whnfType_boxed_2552_ = lean_unbox(v_whnfType_2545_);
v_res_2553_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2540_, v_type_2541_, v_maxFVars_x3f_2542_, v_k_2543_, v_cleanupAnnotations_boxed_2551_, v_whnfType_boxed_2552_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
lean_dec_ref(v___y_2546_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_mvarId_2554_, lean_object* v_x_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2554_, v_x_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
v_a_2570_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2561_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2561_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_mvarId_2578_, lean_object* v_x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_mvarId_2578_, v_x_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2586_, lean_object* v_mvarId_2587_, lean_object* v_x_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_mvarId_2587_, v_x_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2595_, lean_object* v_mvarId_2596_, lean_object* v_x_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2595_, v_mvarId_2596_, v_x_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2604_, lean_object* v_msg_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v_fileName_2611_; lean_object* v_fileMap_2612_; lean_object* v_options_2613_; lean_object* v_currRecDepth_2614_; lean_object* v_maxRecDepth_2615_; lean_object* v_ref_2616_; lean_object* v_currNamespace_2617_; lean_object* v_openDecls_2618_; lean_object* v_initHeartbeats_2619_; lean_object* v_maxHeartbeats_2620_; lean_object* v_quotContext_2621_; lean_object* v_currMacroScope_2622_; uint8_t v_diag_2623_; lean_object* v_cancelTk_x3f_2624_; uint8_t v_suppressElabErrors_2625_; lean_object* v_inheritedTraceOptions_2626_; lean_object* v_ref_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v_fileName_2611_ = lean_ctor_get(v___y_2608_, 0);
v_fileMap_2612_ = lean_ctor_get(v___y_2608_, 1);
v_options_2613_ = lean_ctor_get(v___y_2608_, 2);
v_currRecDepth_2614_ = lean_ctor_get(v___y_2608_, 3);
v_maxRecDepth_2615_ = lean_ctor_get(v___y_2608_, 4);
v_ref_2616_ = lean_ctor_get(v___y_2608_, 5);
v_currNamespace_2617_ = lean_ctor_get(v___y_2608_, 6);
v_openDecls_2618_ = lean_ctor_get(v___y_2608_, 7);
v_initHeartbeats_2619_ = lean_ctor_get(v___y_2608_, 8);
v_maxHeartbeats_2620_ = lean_ctor_get(v___y_2608_, 9);
v_quotContext_2621_ = lean_ctor_get(v___y_2608_, 10);
v_currMacroScope_2622_ = lean_ctor_get(v___y_2608_, 11);
v_diag_2623_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*14);
v_cancelTk_x3f_2624_ = lean_ctor_get(v___y_2608_, 12);
v_suppressElabErrors_2625_ = lean_ctor_get_uint8(v___y_2608_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2626_ = lean_ctor_get(v___y_2608_, 13);
v_ref_2627_ = l_Lean_replaceRef(v_ref_2604_, v_ref_2616_);
lean_inc_ref(v_inheritedTraceOptions_2626_);
lean_inc(v_cancelTk_x3f_2624_);
lean_inc(v_currMacroScope_2622_);
lean_inc(v_quotContext_2621_);
lean_inc(v_maxHeartbeats_2620_);
lean_inc(v_initHeartbeats_2619_);
lean_inc(v_openDecls_2618_);
lean_inc(v_currNamespace_2617_);
lean_inc(v_maxRecDepth_2615_);
lean_inc(v_currRecDepth_2614_);
lean_inc_ref(v_options_2613_);
lean_inc_ref(v_fileMap_2612_);
lean_inc_ref(v_fileName_2611_);
v___x_2628_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2628_, 0, v_fileName_2611_);
lean_ctor_set(v___x_2628_, 1, v_fileMap_2612_);
lean_ctor_set(v___x_2628_, 2, v_options_2613_);
lean_ctor_set(v___x_2628_, 3, v_currRecDepth_2614_);
lean_ctor_set(v___x_2628_, 4, v_maxRecDepth_2615_);
lean_ctor_set(v___x_2628_, 5, v_ref_2627_);
lean_ctor_set(v___x_2628_, 6, v_currNamespace_2617_);
lean_ctor_set(v___x_2628_, 7, v_openDecls_2618_);
lean_ctor_set(v___x_2628_, 8, v_initHeartbeats_2619_);
lean_ctor_set(v___x_2628_, 9, v_maxHeartbeats_2620_);
lean_ctor_set(v___x_2628_, 10, v_quotContext_2621_);
lean_ctor_set(v___x_2628_, 11, v_currMacroScope_2622_);
lean_ctor_set(v___x_2628_, 12, v_cancelTk_x3f_2624_);
lean_ctor_set(v___x_2628_, 13, v_inheritedTraceOptions_2626_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*14, v_diag_2623_);
lean_ctor_set_uint8(v___x_2628_, sizeof(void*)*14 + 1, v_suppressElabErrors_2625_);
v___x_2629_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2605_, v___y_2606_, v___y_2607_, v___x_2628_, v___y_2609_);
lean_dec_ref(v___x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2630_, lean_object* v_msg_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2630_, v_msg_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v_ref_2630_);
return v_res_2637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2642_ = lean_unsigned_to_nat(0u);
v___x_2643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
lean_ctor_set(v___x_2643_, 2, v___x_2642_);
lean_ctor_set(v___x_2643_, 3, v___x_2641_);
lean_ctor_set(v___x_2643_, 4, v___x_2641_);
lean_ctor_set(v___x_2643_, 5, v___x_2641_);
lean_ctor_set(v___x_2643_, 6, v___x_2641_);
lean_ctor_set(v___x_2643_, 7, v___x_2641_);
lean_ctor_set(v___x_2643_, 8, v___x_2641_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_unsigned_to_nat(32u);
v___x_2645_ = lean_mk_empty_array_with_capacity(v___x_2644_);
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2647_ = ((size_t)5ULL);
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_unsigned_to_nat(32u);
v___x_2650_ = lean_mk_empty_array_with_capacity(v___x_2649_);
v___x_2651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2652_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2652_, 0, v___x_2651_);
lean_ctor_set(v___x_2652_, 1, v___x_2650_);
lean_ctor_set(v___x_2652_, 2, v___x_2648_);
lean_ctor_set(v___x_2652_, 3, v___x_2648_);
lean_ctor_set_usize(v___x_2652_, 4, v___x_2647_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = lean_box(1);
v___x_2654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2655_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2656_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2655_);
lean_ctor_set(v___x_2656_, 1, v___x_2654_);
lean_ctor_set(v___x_2656_, 2, v___x_2653_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2659_ = l_Lean_stringToMessageData(v___x_2658_);
return v___x_2659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2665_ = l_Lean_stringToMessageData(v___x_2664_);
return v___x_2665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2668_ = l_Lean_stringToMessageData(v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2671_ = l_Lean_stringToMessageData(v___x_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2674_ = l_Lean_stringToMessageData(v___x_2673_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2677_ = l_Lean_stringToMessageData(v___x_2676_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2678_, lean_object* v_declHint_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v_env_2683_; uint8_t v___x_2684_; 
v___x_2682_ = lean_st_ref_get(v___y_2680_);
v_env_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref(v_env_2683_);
lean_dec(v___x_2682_);
v___x_2684_ = l_Lean_Name_isAnonymous(v_declHint_2679_);
if (v___x_2684_ == 0)
{
uint8_t v_isExporting_2685_; 
v_isExporting_2685_ = lean_ctor_get_uint8(v_env_2683_, sizeof(void*)*8);
if (v_isExporting_2685_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref(v_env_2683_);
lean_dec(v_declHint_2679_);
v___x_2686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2686_, 0, v_msg_2678_);
return v___x_2686_;
}
else
{
lean_object* v___x_2687_; uint8_t v___x_2688_; 
lean_inc_ref(v_env_2683_);
v___x_2687_ = l_Lean_Environment_setExporting(v_env_2683_, v___x_2684_);
lean_inc(v_declHint_2679_);
lean_inc_ref(v___x_2687_);
v___x_2688_ = l_Lean_Environment_contains(v___x_2687_, v_declHint_2679_, v_isExporting_2685_);
if (v___x_2688_ == 0)
{
lean_object* v___x_2689_; 
lean_dec_ref(v___x_2687_);
lean_dec_ref(v_env_2683_);
lean_dec(v_declHint_2679_);
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v_msg_2678_);
return v___x_2689_;
}
else
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v_c_2695_; lean_object* v___x_2696_; 
v___x_2690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2692_ = l_Lean_Options_empty;
v___x_2693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2687_);
lean_ctor_set(v___x_2693_, 1, v___x_2690_);
lean_ctor_set(v___x_2693_, 2, v___x_2691_);
lean_ctor_set(v___x_2693_, 3, v___x_2692_);
lean_inc(v_declHint_2679_);
v___x_2694_ = l_Lean_MessageData_ofConstName(v_declHint_2679_, v___x_2684_);
v_c_2695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2695_, 0, v___x_2693_);
lean_ctor_set(v_c_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2683_, v_declHint_2679_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
lean_dec_ref(v_env_2683_);
lean_dec(v_declHint_2679_);
v___x_2697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v_c_2695_);
v___x_2699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l_Lean_MessageData_note(v___x_2700_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v_msg_2678_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2702_);
return v___x_2703_;
}
else
{
lean_object* v_val_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2739_; 
v_val_2704_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2706_ = v___x_2696_;
v_isShared_2707_ = v_isSharedCheck_2739_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_val_2704_);
lean_dec(v___x_2696_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2739_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v_mod_2711_; uint8_t v___x_2712_; 
v___x_2708_ = lean_box(0);
v___x_2709_ = l_Lean_Environment_header(v_env_2683_);
lean_dec_ref(v_env_2683_);
v___x_2710_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2709_);
v_mod_2711_ = lean_array_get(v___x_2708_, v___x_2710_, v_val_2704_);
lean_dec(v_val_2704_);
lean_dec_ref(v___x_2710_);
v___x_2712_ = l_Lean_isPrivateName(v_declHint_2679_);
lean_dec(v_declHint_2679_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v_c_2695_);
v___x_2715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Lean_MessageData_ofName(v_mod_2711_);
v___x_2718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2716_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_MessageData_note(v___x_2720_);
v___x_2722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_msg_2678_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2722_);
v___x_2724_ = v___x_2706_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
else
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v_c_2695_);
v___x_2728_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2727_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v___x_2730_ = l_Lean_MessageData_ofName(v_mod_2711_);
v___x_2731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2731_);
lean_ctor_set(v___x_2733_, 1, v___x_2732_);
v___x_2734_ = l_Lean_MessageData_note(v___x_2733_);
v___x_2735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2735_, 0, v_msg_2678_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2735_);
v___x_2737_ = v___x_2706_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2740_; 
lean_dec_ref(v_env_2683_);
lean_dec(v_declHint_2679_);
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_msg_2678_);
return v___x_2740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2741_, lean_object* v_declHint_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2741_, v_declHint_2742_, v___y_2743_);
lean_dec(v___y_2743_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2746_, lean_object* v_declHint_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2763_; 
v___x_2753_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2746_, v_declHint_2747_, v___y_2751_);
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2753_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2756_ = v___x_2753_;
v_isShared_2757_ = v_isSharedCheck_2763_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2753_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2763_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2761_; 
v___x_2758_ = l_Lean_unknownIdentifierMessageTag;
v___x_2759_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v_a_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2759_);
v___x_2761_ = v___x_2756_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2759_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2764_, lean_object* v_declHint_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2764_, v_declHint_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2772_, lean_object* v_msg_2773_, lean_object* v_declHint_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; lean_object* v_a_2781_; lean_object* v___x_2782_; 
v___x_2780_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2773_, v_declHint_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref(v___x_2780_);
v___x_2782_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2772_, v_a_2781_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2783_, lean_object* v_msg_2784_, lean_object* v_declHint_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v_res_2791_; 
v_res_2791_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2783_, v_msg_2784_, v_declHint_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v_ref_2783_);
return v_res_2791_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2794_ = l_Lean_stringToMessageData(v___x_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2795_, lean_object* v_constName_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2802_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2803_ = 0;
lean_inc(v_constName_2796_);
v___x_2804_ = l_Lean_MessageData_ofConstName(v_constName_2796_, v___x_2803_);
v___x_2805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2805_, 0, v___x_2802_);
lean_ctor_set(v___x_2805_, 1, v___x_2804_);
v___x_2806_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v___x_2806_);
v___x_2808_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2795_, v___x_2807_, v_constName_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2809_, lean_object* v_constName_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2809_, v_constName_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v_ref_2809_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_ref_2823_; lean_object* v___x_2824_; 
v_ref_2823_ = lean_ctor_get(v___y_2820_, 5);
v___x_2824_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2823_, v_constName_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v___x_2838_; lean_object* v_env_2839_; uint8_t v___x_2840_; lean_object* v___x_2841_; 
v___x_2838_ = lean_st_ref_get(v___y_2836_);
v_env_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc_ref(v_env_2839_);
lean_dec(v___x_2838_);
v___x_2840_ = 0;
lean_inc(v_constName_2832_);
v___x_2841_ = l_Lean_Environment_find_x3f(v_env_2839_, v_constName_2832_, v___x_2840_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
return v___x_2842_;
}
else
{
lean_object* v_val_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_constName_2832_);
v_val_2843_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2841_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_val_2843_);
lean_dec(v___x_2841_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set_tag(v___x_2845_, 0);
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_val_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
return v_res_2857_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2858_, lean_object* v_as_2859_, size_t v_i_2860_, size_t v_stop_2861_){
_start:
{
uint8_t v___x_2862_; 
v___x_2862_ = lean_usize_dec_eq(v_i_2860_, v_stop_2861_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2863_ = lean_array_uget_borrowed(v_as_2859_, v_i_2860_);
v___x_2864_ = l_Lean_Expr_isAppOf(v_e_2858_, v___x_2863_);
if (v___x_2864_ == 0)
{
size_t v___x_2865_; size_t v___x_2866_; 
v___x_2865_ = ((size_t)1ULL);
v___x_2866_ = lean_usize_add(v_i_2860_, v___x_2865_);
v_i_2860_ = v___x_2866_;
goto _start;
}
else
{
return v___x_2864_;
}
}
else
{
uint8_t v___x_2868_; 
v___x_2868_ = 0;
return v___x_2868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2869_, lean_object* v_as_2870_, lean_object* v_i_2871_, lean_object* v_stop_2872_){
_start:
{
size_t v_i_boxed_2873_; size_t v_stop_boxed_2874_; uint8_t v_res_2875_; lean_object* v_r_2876_; 
v_i_boxed_2873_ = lean_unbox_usize(v_i_2871_);
lean_dec(v_i_2871_);
v_stop_boxed_2874_ = lean_unbox_usize(v_stop_2872_);
lean_dec(v_stop_2872_);
v_res_2875_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2869_, v_as_2870_, v_i_boxed_2873_, v_stop_boxed_2874_);
lean_dec_ref(v_as_2870_);
lean_dec_ref(v_e_2869_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2877_, lean_object* v_name_2878_, lean_object* v_levels_2879_, lean_object* v_params_2880_, lean_object* v___y_2881_, lean_object* v___x_2882_, lean_object* v_e_2883_){
_start:
{
uint8_t v___x_2884_; 
v___x_2884_ = l_Lean_Expr_isApp(v_e_2883_);
if (v___x_2884_ == 0)
{
lean_object* v___x_2885_; 
lean_dec_ref(v_e_2883_);
lean_dec_ref(v_params_2880_);
lean_dec(v_levels_2879_);
lean_dec(v_name_2878_);
lean_dec(v_numParams_2877_);
v___x_2885_ = lean_box(0);
return v___x_2885_;
}
else
{
lean_object* v_dummy_2886_; lean_object* v_nargs_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; uint8_t v___y_2895_; uint8_t v___x_2905_; 
v_dummy_2886_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___closed__0);
v_nargs_2887_ = l_Lean_Expr_getAppNumArgs(v_e_2883_);
lean_inc(v_nargs_2887_);
v___x_2888_ = lean_mk_array(v_nargs_2887_, v_dummy_2886_);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_sub(v_nargs_2887_, v___x_2889_);
lean_dec(v_nargs_2887_);
lean_inc_ref(v_e_2883_);
v___x_2891_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2883_, v___x_2888_, v___x_2890_);
v___x_2892_ = lean_array_get_size(v___x_2891_);
v___x_2893_ = l_Array_toSubarray___redArg(v___x_2891_, v_numParams_2877_, v___x_2892_);
v___x_2905_ = l_Lean_Expr_isAppOf(v_e_2883_, v_name_2878_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
lean_dec(v_name_2878_);
v___x_2906_ = lean_array_get_size(v___y_2881_);
v___x_2907_ = lean_nat_dec_lt(v___x_2882_, v___x_2906_);
if (v___x_2907_ == 0)
{
v___y_2895_ = v___x_2905_;
goto v___jp_2894_;
}
else
{
if (v___x_2907_ == 0)
{
v___y_2895_ = v___x_2905_;
goto v___jp_2894_;
}
else
{
size_t v___x_2908_; size_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2908_ = ((size_t)0ULL);
v___x_2909_ = lean_usize_of_nat(v___x_2906_);
v___x_2910_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2883_, v___y_2881_, v___x_2908_, v___x_2909_);
v___y_2895_ = v___x_2910_;
goto v___jp_2894_;
}
}
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
lean_dec_ref(v_e_2883_);
v___x_2911_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2878_);
v___x_2912_ = l_Lean_mkConst(v___x_2911_, v_levels_2879_);
v___x_2913_ = l_Subarray_copy___redArg(v___x_2893_);
v___x_2914_ = l_Array_append___redArg(v_params_2880_, v___x_2913_);
lean_dec_ref(v___x_2913_);
v___x_2915_ = l_Lean_mkAppN(v___x_2912_, v___x_2914_);
lean_dec_ref(v___x_2914_);
v___x_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2916_, 0, v___x_2915_);
return v___x_2916_;
}
v___jp_2894_:
{
if (v___y_2895_ == 0)
{
lean_object* v___x_2896_; 
lean_dec_ref(v___x_2893_);
lean_dec_ref(v_e_2883_);
lean_dec_ref(v_params_2880_);
lean_dec(v_levels_2879_);
v___x_2896_ = lean_box(0);
return v___x_2896_;
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2897_ = l_Lean_Expr_getAppFn(v_e_2883_);
lean_dec_ref(v_e_2883_);
v___x_2898_ = l_Lean_Expr_constName(v___x_2897_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2898_);
v___x_2900_ = l_Lean_mkConst(v___x_2899_, v_levels_2879_);
v___x_2901_ = l_Subarray_copy___redArg(v___x_2893_);
v___x_2902_ = l_Array_append___redArg(v_params_2880_, v___x_2901_);
lean_dec_ref(v___x_2901_);
v___x_2903_ = l_Lean_mkAppN(v___x_2900_, v___x_2902_);
lean_dec_ref(v___x_2902_);
v___x_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2903_);
return v___x_2904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2917_, lean_object* v_name_2918_, lean_object* v_levels_2919_, lean_object* v_params_2920_, lean_object* v___y_2921_, lean_object* v___x_2922_, lean_object* v_e_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2917_, v_name_2918_, v_levels_2919_, v_params_2920_, v___y_2921_, v___x_2922_, v_e_2923_);
lean_dec(v___x_2922_);
lean_dec_ref(v___y_2921_);
return v_res_2924_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__0));
v___x_2927_ = l_Lean_stringToMessageData(v___x_2926_);
return v___x_2927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__9));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(lean_object* v___x_2951_, lean_object* v___x_2952_, uint8_t v___x_2953_, lean_object* v___x_2954_, lean_object* v___x_2955_, uint8_t v___x_2956_, lean_object* v___x_2957_, lean_object* v_params_2958_, lean_object* v_args_2959_, lean_object* v_indices_2960_, uint8_t v___x_2961_, lean_object* v___x_2962_, lean_object* v_a_2963_, lean_object* v___x_2964_, lean_object* v_targetArgs_2965_, lean_object* v_x_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; uint8_t v___x_2973_; 
v___x_2972_ = lean_array_get_size(v_targetArgs_2965_);
v___x_2973_ = lean_nat_dec_eq(v___x_2972_, v___x_2951_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v___x_2952_);
v___x_2974_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1);
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
lean_inc_ref(v___x_2952_);
v___x_2976_ = lean_infer_type(v___x_2952_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
lean_dec_ref(v___x_2976_);
if (lean_obj_tag(v_a_2977_) == 7)
{
lean_object* v_binderType_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v_binderType_2978_ = lean_ctor_get(v_a_2977_, 1);
lean_inc_ref(v_binderType_2978_);
lean_dec_ref(v_a_2977_);
v___x_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2979_, 0, v_binderType_2978_);
v___x_2980_ = l_Lean_Meta_mkFreshExprMVar(v___x_2979_, v___x_2953_, v___x_2954_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref(v___x_2980_);
v___x_2982_ = l_Lean_Expr_mvarId_x21(v_a_2981_);
v___x_2983_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2982_, v___x_2955_, v___x_2956_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref(v___x_2983_);
v___x_2985_ = lean_array_fget_borrowed(v_targetArgs_2965_, v___x_2957_);
lean_inc(v___x_2985_);
v___x_2986_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2984_, v___x_2985_, v___y_2968_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3046_; 
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; 
v_unused_3047_ = lean_ctor_get(v___x_2986_, 0);
lean_dec(v_unused_3047_);
v___x_2988_ = v___x_2986_;
v_isShared_2989_ = v_isSharedCheck_3046_;
goto v_resetjp_2987_;
}
else
{
lean_dec(v___x_2986_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3046_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; uint8_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2990_ = l_Lean_Expr_app___override(v___x_2952_, v_a_2981_);
lean_inc_ref(v_params_2958_);
v___x_2991_ = l_Array_append___redArg(v_params_2958_, v_args_2959_);
v___x_2992_ = l_Array_append___redArg(v___x_2991_, v_indices_2960_);
v___x_2993_ = l_Array_append___redArg(v___x_2992_, v_targetArgs_2965_);
v___x_2994_ = 1;
v___x_2995_ = l_Lean_Meta_mkLambdaFVars(v___x_2993_, v___x_2990_, v___x_2961_, v___x_2956_, v___x_2961_, v___x_2956_, v___x_2994_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec_ref(v___x_2993_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref(v___x_2995_);
v___x_2997_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_2996_, v___y_2968_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = l_Lean_Meta_mkForallFVars(v_params_2958_, v___x_2962_, v___x_2961_, v___x_2956_, v___x_2956_, v___x_2994_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec_ref(v_params_2958_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = l_Lean_ConstantInfo_levelParams(v_a_2963_);
v___x_3002_ = l_Lean_mkCasesOnName(v___x_2964_);
v___x_3003_ = lean_box(0);
lean_inc(v___x_3002_);
v___x_3004_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_3002_, v___x_3001_, v_a_3000_, v_a_2998_, v___x_3003_, v___y_2970_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref(v___x_3004_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set_tag(v___x_2988_, 1);
lean_ctor_set(v___x_2988_, 0, v_a_3005_);
v___x_3007_ = v___x_2988_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3005_);
v___x_3007_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Lean_addDecl(v___x_3007_, v___x_2961_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___x_3008_);
v___x_3009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__8));
v___x_3010_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3010_, 0, v___x_3002_);
lean_closure_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_3011_, 0, lean_box(0));
lean_closure_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = l_Lean_liftCommandElabM___redArg(v___x_3011_, v___x_2956_, v___y_2969_, v___y_2970_);
return v___x_3012_;
}
else
{
lean_dec(v___x_3002_);
return v___x_3008_;
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v___x_3002_);
lean_del_object(v___x_2988_);
v_a_3014_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_3004_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_3004_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_dec(v_a_2998_);
lean_del_object(v___x_2988_);
lean_dec(v___x_2964_);
v_a_3022_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2999_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2999_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_2988_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
v_a_3030_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2997_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2997_);
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
lean_del_object(v___x_2988_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
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
}
else
{
lean_dec(v_a_2981_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2952_);
return v___x_2986_;
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_2981_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2952_);
v_a_3048_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2983_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2983_);
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
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec_ref(v___x_2952_);
v_a_3056_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2980_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2980_);
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
else
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
lean_dec(v_a_2977_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v___x_2952_);
v___x_3064_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10);
v___x_3065_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3064_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
return v___x_3065_;
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v___x_2952_);
v_a_3066_ = lean_ctor_get(v___x_2976_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2976_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2976_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object** _args){
lean_object* v___x_3074_ = _args[0];
lean_object* v___x_3075_ = _args[1];
lean_object* v___x_3076_ = _args[2];
lean_object* v___x_3077_ = _args[3];
lean_object* v___x_3078_ = _args[4];
lean_object* v___x_3079_ = _args[5];
lean_object* v___x_3080_ = _args[6];
lean_object* v_params_3081_ = _args[7];
lean_object* v_args_3082_ = _args[8];
lean_object* v_indices_3083_ = _args[9];
lean_object* v___x_3084_ = _args[10];
lean_object* v___x_3085_ = _args[11];
lean_object* v_a_3086_ = _args[12];
lean_object* v___x_3087_ = _args[13];
lean_object* v_targetArgs_3088_ = _args[14];
lean_object* v_x_3089_ = _args[15];
lean_object* v___y_3090_ = _args[16];
lean_object* v___y_3091_ = _args[17];
lean_object* v___y_3092_ = _args[18];
lean_object* v___y_3093_ = _args[19];
lean_object* v___y_3094_ = _args[20];
_start:
{
uint8_t v___x_13949__boxed_3095_; uint8_t v___x_13952__boxed_3096_; uint8_t v___x_13954__boxed_3097_; lean_object* v_res_3098_; 
v___x_13949__boxed_3095_ = lean_unbox(v___x_3076_);
v___x_13952__boxed_3096_ = lean_unbox(v___x_3079_);
v___x_13954__boxed_3097_ = lean_unbox(v___x_3084_);
v_res_3098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_3074_, v___x_3075_, v___x_13949__boxed_3095_, v___x_3077_, v___x_3078_, v___x_13952__boxed_3096_, v___x_3080_, v_params_3081_, v_args_3082_, v_indices_3083_, v___x_13954__boxed_3097_, v___x_3085_, v_a_3086_, v___x_3087_, v_targetArgs_3088_, v_x_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v_x_3089_);
lean_dec_ref(v_targetArgs_3088_);
lean_dec_ref(v_a_3086_);
lean_dec_ref(v_indices_3083_);
lean_dec_ref(v_args_3082_);
lean_dec(v___x_3080_);
lean_dec(v___x_3074_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v___x_3099_, lean_object* v___x_3100_, uint8_t v___x_3101_, lean_object* v___x_3102_, lean_object* v___x_3103_, uint8_t v___x_3104_, lean_object* v___x_3105_, lean_object* v_params_3106_, lean_object* v_args_3107_, uint8_t v___x_3108_, lean_object* v___x_3109_, lean_object* v_a_3110_, lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v_indices_3113_, lean_object* v_goalType_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___f_3124_; lean_object* v___x_3125_; 
v___x_3120_ = l_Lean_mkAppN(v___x_3099_, v_indices_3113_);
v___x_3121_ = lean_box(v___x_3101_);
v___x_3122_ = lean_box(v___x_3104_);
v___x_3123_ = lean_box(v___x_3108_);
v___f_3124_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed), 21, 14);
lean_closure_set(v___f_3124_, 0, v___x_3100_);
lean_closure_set(v___f_3124_, 1, v___x_3120_);
lean_closure_set(v___f_3124_, 2, v___x_3121_);
lean_closure_set(v___f_3124_, 3, v___x_3102_);
lean_closure_set(v___f_3124_, 4, v___x_3103_);
lean_closure_set(v___f_3124_, 5, v___x_3122_);
lean_closure_set(v___f_3124_, 6, v___x_3105_);
lean_closure_set(v___f_3124_, 7, v_params_3106_);
lean_closure_set(v___f_3124_, 8, v_args_3107_);
lean_closure_set(v___f_3124_, 9, v_indices_3113_);
lean_closure_set(v___f_3124_, 10, v___x_3123_);
lean_closure_set(v___f_3124_, 11, v___x_3109_);
lean_closure_set(v___f_3124_, 12, v_a_3110_);
lean_closure_set(v___f_3124_, 13, v___x_3111_);
v___x_3125_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_goalType_3114_, v___x_3112_, v___f_3124_, v___x_3108_, v___x_3108_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object** _args){
lean_object* v___x_3126_ = _args[0];
lean_object* v___x_3127_ = _args[1];
lean_object* v___x_3128_ = _args[2];
lean_object* v___x_3129_ = _args[3];
lean_object* v___x_3130_ = _args[4];
lean_object* v___x_3131_ = _args[5];
lean_object* v___x_3132_ = _args[6];
lean_object* v_params_3133_ = _args[7];
lean_object* v_args_3134_ = _args[8];
lean_object* v___x_3135_ = _args[9];
lean_object* v___x_3136_ = _args[10];
lean_object* v_a_3137_ = _args[11];
lean_object* v___x_3138_ = _args[12];
lean_object* v___x_3139_ = _args[13];
lean_object* v_indices_3140_ = _args[14];
lean_object* v_goalType_3141_ = _args[15];
lean_object* v___y_3142_ = _args[16];
lean_object* v___y_3143_ = _args[17];
lean_object* v___y_3144_ = _args[18];
lean_object* v___y_3145_ = _args[19];
lean_object* v___y_3146_ = _args[20];
_start:
{
uint8_t v___x_14237__boxed_3147_; uint8_t v___x_14240__boxed_3148_; uint8_t v___x_14242__boxed_3149_; lean_object* v_res_3150_; 
v___x_14237__boxed_3147_ = lean_unbox(v___x_3128_);
v___x_14240__boxed_3148_ = lean_unbox(v___x_3131_);
v___x_14242__boxed_3149_ = lean_unbox(v___x_3135_);
v_res_3150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v___x_3126_, v___x_3127_, v___x_14237__boxed_3147_, v___x_3129_, v___x_3130_, v___x_14240__boxed_3148_, v___x_3132_, v_params_3133_, v_args_3134_, v___x_14242__boxed_3149_, v___x_3136_, v_a_3137_, v___x_3138_, v___x_3139_, v_indices_3140_, v_goalType_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_3151_, uint8_t v___x_3152_, lean_object* v_snd_3153_, lean_object* v___x_3154_, uint8_t v___x_3155_, lean_object* v___x_3156_, lean_object* v___x_3157_, lean_object* v_a_3158_, lean_object* v___x_3159_, uint8_t v___x_3160_, lean_object* v___x_3161_, lean_object* v___x_3162_, lean_object* v_params_3163_, lean_object* v_args_3164_, lean_object* v___x_3165_, lean_object* v_a_3166_, lean_object* v___x_3167_, lean_object* v___x_3168_, lean_object* v_numIndices_3169_, lean_object* v_goalType_3170_, lean_object* v___x_3171_, lean_object* v___x_3172_, lean_object* v_fst_3173_, lean_object* v___x_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_lctx_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v_lctx_3180_ = lean_ctor_get(v___y_3175_, 2);
lean_inc(v___x_3151_);
lean_inc_ref(v_lctx_3180_);
v___x_3181_ = l_Lean_LocalContext_get_x21(v_lctx_3180_, v___x_3151_);
v___x_3182_ = l_Lean_LocalDecl_type(v___x_3181_);
lean_dec_ref(v___x_3181_);
v___x_3183_ = 2;
v___x_3184_ = lean_box(0);
v___x_3185_ = 0;
v___x_3186_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*1, v___x_3183_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*1 + 1, v___x_3152_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*1 + 2, v___x_3185_);
lean_inc_ref(v___x_3154_);
lean_inc(v_snd_3153_);
v___x_3187_ = l_Lean_MVarId_rewrite(v_snd_3153_, v___x_3182_, v___x_3154_, v___x_3152_, v___x_3186_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v_a_3188_; lean_object* v_eNew_3189_; lean_object* v_eqProof_3190_; lean_object* v___x_3191_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_a_3188_);
lean_dec_ref(v___x_3187_);
v_eNew_3189_ = lean_ctor_get(v_a_3188_, 0);
lean_inc_ref(v_eNew_3189_);
v_eqProof_3190_ = lean_ctor_get(v_a_3188_, 1);
lean_inc_ref(v_eqProof_3190_);
lean_dec(v_a_3188_);
v___x_3191_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_snd_3153_, v___x_3151_, v_eNew_3189_, v_eqProof_3190_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___y_3194_; uint8_t v___x_3222_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref(v___x_3191_);
v___x_3222_ = lean_nat_dec_lt(v___x_3171_, v___x_3172_);
if (v___x_3222_ == 0)
{
v___y_3194_ = v_fst_3173_;
goto v___jp_3193_;
}
else
{
lean_object* v_fvarId_3223_; lean_object* v_xs_x27_3224_; lean_object* v___x_3225_; 
v_fvarId_3223_ = lean_ctor_get(v_a_3192_, 0);
v_xs_x27_3224_ = lean_array_fset(v_fst_3173_, v___x_3171_, v___x_3174_);
lean_inc(v_fvarId_3223_);
v___x_3225_ = lean_array_fset(v_xs_x27_3224_, v___x_3171_, v_fvarId_3223_);
v___y_3194_ = v___x_3225_;
goto v___jp_3193_;
}
v___jp_3193_:
{
lean_object* v_mvarId_3195_; lean_object* v___x_3196_; 
v_mvarId_3195_ = lean_ctor_get(v_a_3192_, 1);
lean_inc(v_mvarId_3195_);
lean_dec(v_a_3192_);
v___x_3196_ = l_Lean_MVarId_revert(v_mvarId_3195_, v___y_3194_, v___x_3155_, v___x_3155_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v_snd_3198_; lean_object* v___x_3199_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref(v___x_3196_);
v_snd_3198_ = lean_ctor_get(v_a_3197_, 1);
lean_inc(v_snd_3198_);
lean_dec(v_a_3197_);
v___x_3199_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3198_, v___x_3156_, v___y_3176_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3212_; 
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3212_ == 0)
{
lean_object* v_unused_3213_; 
v_unused_3213_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3213_);
v___x_3201_ = v___x_3199_;
v_isShared_3202_ = v_isSharedCheck_3212_;
goto v_resetjp_3200_;
}
else
{
lean_dec(v___x_3199_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3212_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___f_3207_; lean_object* v___x_3209_; 
v___x_3203_ = l_Lean_Expr_app___override(v___x_3157_, v_a_3158_);
v___x_3204_ = lean_box(v___x_3160_);
v___x_3205_ = lean_box(v___x_3152_);
v___x_3206_ = lean_box(v___x_3155_);
v___f_3207_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 21, 14);
lean_closure_set(v___f_3207_, 0, v___x_3203_);
lean_closure_set(v___f_3207_, 1, v___x_3159_);
lean_closure_set(v___f_3207_, 2, v___x_3204_);
lean_closure_set(v___f_3207_, 3, v___x_3161_);
lean_closure_set(v___f_3207_, 4, v___x_3154_);
lean_closure_set(v___f_3207_, 5, v___x_3205_);
lean_closure_set(v___f_3207_, 6, v___x_3162_);
lean_closure_set(v___f_3207_, 7, v_params_3163_);
lean_closure_set(v___f_3207_, 8, v_args_3164_);
lean_closure_set(v___f_3207_, 9, v___x_3206_);
lean_closure_set(v___f_3207_, 10, v___x_3165_);
lean_closure_set(v___f_3207_, 11, v_a_3166_);
lean_closure_set(v___f_3207_, 12, v___x_3167_);
lean_closure_set(v___f_3207_, 13, v___x_3168_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set_tag(v___x_3201_, 1);
lean_ctor_set(v___x_3201_, 0, v_numIndices_3169_);
v___x_3209_ = v___x_3201_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_numIndices_3169_);
v___x_3209_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_goalType_3170_, v___x_3209_, v___f_3207_, v___x_3155_, v___x_3155_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec_ref(v___y_3175_);
return v___x_3210_;
}
}
}
else
{
lean_dec_ref(v___y_3175_);
lean_dec_ref(v_goalType_3170_);
lean_dec(v_numIndices_3169_);
lean_dec(v___x_3168_);
lean_dec(v___x_3167_);
lean_dec_ref(v_a_3166_);
lean_dec_ref(v___x_3165_);
lean_dec_ref(v_args_3164_);
lean_dec_ref(v_params_3163_);
lean_dec(v___x_3162_);
lean_dec(v___x_3161_);
lean_dec(v___x_3159_);
lean_dec_ref(v_a_3158_);
lean_dec_ref(v___x_3157_);
lean_dec_ref(v___x_3154_);
return v___x_3199_;
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec_ref(v___y_3175_);
lean_dec_ref(v_goalType_3170_);
lean_dec(v_numIndices_3169_);
lean_dec(v___x_3168_);
lean_dec(v___x_3167_);
lean_dec_ref(v_a_3166_);
lean_dec_ref(v___x_3165_);
lean_dec_ref(v_args_3164_);
lean_dec_ref(v_params_3163_);
lean_dec(v___x_3162_);
lean_dec(v___x_3161_);
lean_dec(v___x_3159_);
lean_dec_ref(v_a_3158_);
lean_dec_ref(v___x_3157_);
lean_dec_ref(v___x_3156_);
lean_dec_ref(v___x_3154_);
v_a_3214_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3196_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3196_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_dec_ref(v___y_3175_);
lean_dec_ref(v_fst_3173_);
lean_dec_ref(v_goalType_3170_);
lean_dec(v_numIndices_3169_);
lean_dec(v___x_3168_);
lean_dec(v___x_3167_);
lean_dec_ref(v_a_3166_);
lean_dec_ref(v___x_3165_);
lean_dec_ref(v_args_3164_);
lean_dec_ref(v_params_3163_);
lean_dec(v___x_3162_);
lean_dec(v___x_3161_);
lean_dec(v___x_3159_);
lean_dec_ref(v_a_3158_);
lean_dec_ref(v___x_3157_);
lean_dec_ref(v___x_3156_);
lean_dec_ref(v___x_3154_);
v_a_3226_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3191_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3191_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v___y_3175_);
lean_dec_ref(v_fst_3173_);
lean_dec_ref(v_goalType_3170_);
lean_dec(v_numIndices_3169_);
lean_dec(v___x_3168_);
lean_dec(v___x_3167_);
lean_dec_ref(v_a_3166_);
lean_dec_ref(v___x_3165_);
lean_dec_ref(v_args_3164_);
lean_dec_ref(v_params_3163_);
lean_dec(v___x_3162_);
lean_dec(v___x_3161_);
lean_dec(v___x_3159_);
lean_dec_ref(v_a_3158_);
lean_dec_ref(v___x_3157_);
lean_dec_ref(v___x_3156_);
lean_dec_ref(v___x_3154_);
lean_dec(v_snd_3153_);
lean_dec(v___x_3151_);
v_a_3234_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3187_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3187_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3242_ = _args[0];
lean_object* v___x_3243_ = _args[1];
lean_object* v_snd_3244_ = _args[2];
lean_object* v___x_3245_ = _args[3];
lean_object* v___x_3246_ = _args[4];
lean_object* v___x_3247_ = _args[5];
lean_object* v___x_3248_ = _args[6];
lean_object* v_a_3249_ = _args[7];
lean_object* v___x_3250_ = _args[8];
lean_object* v___x_3251_ = _args[9];
lean_object* v___x_3252_ = _args[10];
lean_object* v___x_3253_ = _args[11];
lean_object* v_params_3254_ = _args[12];
lean_object* v_args_3255_ = _args[13];
lean_object* v___x_3256_ = _args[14];
lean_object* v_a_3257_ = _args[15];
lean_object* v___x_3258_ = _args[16];
lean_object* v___x_3259_ = _args[17];
lean_object* v_numIndices_3260_ = _args[18];
lean_object* v_goalType_3261_ = _args[19];
lean_object* v___x_3262_ = _args[20];
lean_object* v___x_3263_ = _args[21];
lean_object* v_fst_3264_ = _args[22];
lean_object* v___x_3265_ = _args[23];
lean_object* v___y_3266_ = _args[24];
lean_object* v___y_3267_ = _args[25];
lean_object* v___y_3268_ = _args[26];
lean_object* v___y_3269_ = _args[27];
lean_object* v___y_3270_ = _args[28];
_start:
{
uint8_t v___x_14299__boxed_3271_; uint8_t v___x_14302__boxed_3272_; uint8_t v___x_14307__boxed_3273_; lean_object* v_res_3274_; 
v___x_14299__boxed_3271_ = lean_unbox(v___x_3243_);
v___x_14302__boxed_3272_ = lean_unbox(v___x_3246_);
v___x_14307__boxed_3273_ = lean_unbox(v___x_3251_);
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3242_, v___x_14299__boxed_3271_, v_snd_3244_, v___x_3245_, v___x_14302__boxed_3272_, v___x_3247_, v___x_3248_, v_a_3249_, v___x_3250_, v___x_14307__boxed_3273_, v___x_3252_, v___x_3253_, v_params_3254_, v_args_3255_, v___x_3256_, v_a_3257_, v___x_3258_, v___x_3259_, v_numIndices_3260_, v_goalType_3261_, v___x_3262_, v___x_3263_, v_fst_3264_, v___x_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec(v___x_3263_);
lean_dec(v___x_3262_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3275_, lean_object* v_a_3276_, lean_object* v_numIndices_3277_, lean_object* v___x_3278_, lean_object* v___x_3279_, lean_object* v___x_3280_, lean_object* v___x_3281_, lean_object* v_params_3282_, lean_object* v___x_3283_, lean_object* v_a_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v___x_3287_, lean_object* v_args_3288_, lean_object* v_goalType_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = lean_array_get_size(v_args_3288_);
v___x_3296_ = lean_nat_dec_eq(v___x_3295_, v___x_3275_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec_ref(v_goalType_3289_);
lean_dec_ref(v_args_3288_);
lean_dec(v___x_3286_);
lean_dec(v___x_3285_);
lean_dec_ref(v_a_3284_);
lean_dec_ref(v___x_3283_);
lean_dec_ref(v_params_3282_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
lean_dec(v_numIndices_3277_);
lean_dec(v___x_3275_);
v___x_3297_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1);
v___x_3298_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3297_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3298_;
}
else
{
if (lean_obj_tag(v_a_3276_) == 7)
{
lean_object* v_binderType_3299_; lean_object* v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_binderType_3299_ = lean_ctor_get(v_a_3276_, 1);
lean_inc_ref(v_binderType_3299_);
v___x_3300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3300_, 0, v_binderType_3299_);
v___x_3301_ = 0;
v___x_3302_ = lean_box(0);
v___x_3303_ = l_Lean_Meta_mkFreshExprMVar(v___x_3300_, v___x_3301_, v___x_3302_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = l_Lean_Expr_mvarId_x21(v_a_3304_);
v___x_3306_ = lean_nat_add(v_numIndices_3277_, v___x_3275_);
v___x_3307_ = lean_box(0);
v___x_3308_ = 0;
v___x_3309_ = l_Lean_Meta_introNCore(v___x_3305_, v___x_3306_, v___x_3307_, v___x_3308_, v___x_3308_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v_fst_3311_; lean_object* v_snd_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___f_3320_; lean_object* v___x_3321_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref(v___x_3309_);
v_fst_3311_ = lean_ctor_get(v_a_3310_, 0);
lean_inc(v_fst_3311_);
v_snd_3312_ = lean_ctor_get(v_a_3310_, 1);
lean_inc(v_snd_3312_);
lean_dec(v_a_3310_);
v___x_3313_ = lean_array_fget(v_args_3288_, v___x_3278_);
v___x_3314_ = lean_array_get_size(v_fst_3311_);
v___x_3315_ = lean_nat_sub(v___x_3314_, v___x_3275_);
v___x_3316_ = lean_array_get(v___x_3279_, v_fst_3311_, v___x_3315_);
v___x_3317_ = lean_box(v___x_3296_);
v___x_3318_ = lean_box(v___x_3308_);
v___x_3319_ = lean_box(v___x_3301_);
lean_inc(v_snd_3312_);
v___f_3320_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 29, 24);
lean_closure_set(v___f_3320_, 0, v___x_3316_);
lean_closure_set(v___f_3320_, 1, v___x_3317_);
lean_closure_set(v___f_3320_, 2, v_snd_3312_);
lean_closure_set(v___f_3320_, 3, v___x_3280_);
lean_closure_set(v___f_3320_, 4, v___x_3318_);
lean_closure_set(v___f_3320_, 5, v___x_3313_);
lean_closure_set(v___f_3320_, 6, v___x_3281_);
lean_closure_set(v___f_3320_, 7, v_a_3304_);
lean_closure_set(v___f_3320_, 8, v___x_3275_);
lean_closure_set(v___f_3320_, 9, v___x_3319_);
lean_closure_set(v___f_3320_, 10, v___x_3302_);
lean_closure_set(v___f_3320_, 11, v___x_3278_);
lean_closure_set(v___f_3320_, 12, v_params_3282_);
lean_closure_set(v___f_3320_, 13, v_args_3288_);
lean_closure_set(v___f_3320_, 14, v___x_3283_);
lean_closure_set(v___f_3320_, 15, v_a_3284_);
lean_closure_set(v___f_3320_, 16, v___x_3285_);
lean_closure_set(v___f_3320_, 17, v___x_3286_);
lean_closure_set(v___f_3320_, 18, v_numIndices_3277_);
lean_closure_set(v___f_3320_, 19, v_goalType_3289_);
lean_closure_set(v___f_3320_, 20, v___x_3315_);
lean_closure_set(v___f_3320_, 21, v___x_3314_);
lean_closure_set(v___f_3320_, 22, v_fst_3311_);
lean_closure_set(v___f_3320_, 23, v___x_3287_);
v___x_3321_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_snd_3312_, v___f_3320_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3321_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_dec(v_a_3304_);
lean_dec_ref(v_goalType_3289_);
lean_dec_ref(v_args_3288_);
lean_dec(v___x_3286_);
lean_dec(v___x_3285_);
lean_dec_ref(v_a_3284_);
lean_dec_ref(v___x_3283_);
lean_dec_ref(v_params_3282_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
lean_dec(v_numIndices_3277_);
lean_dec(v___x_3275_);
v_a_3322_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3309_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3309_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_dec_ref(v_goalType_3289_);
lean_dec_ref(v_args_3288_);
lean_dec(v___x_3286_);
lean_dec(v___x_3285_);
lean_dec_ref(v_a_3284_);
lean_dec_ref(v___x_3283_);
lean_dec_ref(v_params_3282_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
lean_dec(v_numIndices_3277_);
lean_dec(v___x_3275_);
v_a_3330_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3303_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3303_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
else
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec_ref(v_goalType_3289_);
lean_dec_ref(v_args_3288_);
lean_dec(v___x_3286_);
lean_dec(v___x_3285_);
lean_dec_ref(v_a_3284_);
lean_dec_ref(v___x_3283_);
lean_dec_ref(v_params_3282_);
lean_dec_ref(v___x_3281_);
lean_dec_ref(v___x_3280_);
lean_dec(v___x_3279_);
lean_dec(v___x_3278_);
lean_dec(v_numIndices_3277_);
lean_dec(v___x_3275_);
v___x_3338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10);
v___x_3339_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3338_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
return v___x_3339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3340_ = _args[0];
lean_object* v_a_3341_ = _args[1];
lean_object* v_numIndices_3342_ = _args[2];
lean_object* v___x_3343_ = _args[3];
lean_object* v___x_3344_ = _args[4];
lean_object* v___x_3345_ = _args[5];
lean_object* v___x_3346_ = _args[6];
lean_object* v_params_3347_ = _args[7];
lean_object* v___x_3348_ = _args[8];
lean_object* v_a_3349_ = _args[9];
lean_object* v___x_3350_ = _args[10];
lean_object* v___x_3351_ = _args[11];
lean_object* v___x_3352_ = _args[12];
lean_object* v_args_3353_ = _args[13];
lean_object* v_goalType_3354_ = _args[14];
lean_object* v___y_3355_ = _args[15];
lean_object* v___y_3356_ = _args[16];
lean_object* v___y_3357_ = _args[17];
lean_object* v___y_3358_ = _args[18];
lean_object* v___y_3359_ = _args[19];
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3340_, v_a_3341_, v_numIndices_3342_, v___x_3343_, v___x_3344_, v___x_3345_, v___x_3346_, v_params_3347_, v___x_3348_, v_a_3349_, v___x_3350_, v___x_3351_, v___x_3352_, v_args_3353_, v_goalType_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec_ref(v_a_3341_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v_env_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; 
v___x_3367_ = lean_st_ref_get(v___y_3365_);
v_env_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc_ref(v_env_3368_);
lean_dec(v___x_3367_);
v___x_3369_ = 0;
lean_inc(v_constName_3361_);
v___x_3370_ = l_Lean_Environment_findConstVal_x3f(v_env_3368_, v_constName_3361_, v___x_3369_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v___x_3371_; 
v___x_3371_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
return v___x_3371_;
}
else
{
lean_object* v_val_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3379_; 
lean_dec(v_constName_3361_);
v_val_3372_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3374_ = v___x_3370_;
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_val_3372_);
lean_dec(v___x_3370_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3379_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3377_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set_tag(v___x_3374_, 0);
v___x_3377_ = v___x_3374_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_val_3372_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___x_3393_; 
lean_inc(v_constName_3387_);
v___x_3393_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3405_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3405_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3405_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v_levelParams_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3403_; 
v_levelParams_3398_ = lean_ctor_get(v_a_3394_, 1);
lean_inc(v_levelParams_3398_);
lean_dec(v_a_3394_);
v___x_3399_ = lean_box(0);
v___x_3400_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3398_, v___x_3399_);
v___x_3401_ = l_Lean_mkConst(v_constName_3387_, v___x_3400_);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3401_);
v___x_3403_ = v___x_3396_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec(v_constName_3387_);
v_a_3406_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3393_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3393_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v_levels_3423_, lean_object* v_params_3424_, lean_object* v___y_3425_, lean_object* v_predicates_3426_, lean_object* v_as_3427_, size_t v_sz_3428_, size_t v_i_3429_, lean_object* v_b_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_usize_dec_lt(v_i_3429_, v_sz_3428_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; 
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_params_3424_);
lean_dec(v_levels_3423_);
v___x_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3437_, 0, v_b_3430_);
return v___x_3437_;
}
else
{
lean_object* v_a_3438_; lean_object* v_toConstantVal_3439_; lean_object* v_numParams_3440_; lean_object* v_numIndices_3441_; lean_object* v_name_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v_a_3438_ = lean_array_uget_borrowed(v_as_3427_, v_i_3429_);
v_toConstantVal_3439_ = lean_ctor_get(v_a_3438_, 0);
v_numParams_3440_ = lean_ctor_get(v_a_3438_, 1);
v_numIndices_3441_ = lean_ctor_get(v_a_3438_, 2);
v_name_3442_ = lean_ctor_get(v_toConstantVal_3439_, 0);
lean_inc(v_name_3442_);
v___x_3443_ = l_Lean_mkCasesOnName(v_name_3442_);
lean_inc(v___x_3443_);
v___x_3444_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3443_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3446_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
lean_inc(v_a_3445_);
lean_dec_ref(v___x_3444_);
v___x_3446_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3443_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
lean_inc_ref(v_params_3424_);
v___x_3448_ = l_Array_append___redArg(v_params_3424_, v_predicates_3426_);
v___x_3449_ = l_Lean_mkAppN(v_a_3447_, v___x_3448_);
lean_dec_ref(v___x_3448_);
lean_inc(v___y_3434_);
lean_inc_ref(v___y_3433_);
lean_inc(v___y_3432_);
lean_inc_ref(v___y_3431_);
lean_inc_ref(v___x_3449_);
v___x_3450_ = lean_infer_type(v___x_3449_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3452_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref(v___x_3450_);
lean_inc(v___y_3434_);
lean_inc_ref(v___y_3433_);
lean_inc(v___y_3432_);
lean_inc_ref(v___y_3431_);
lean_inc_ref(v___x_3449_);
v___x_3452_ = lean_infer_type(v___x_3449_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___f_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; uint8_t v___x_3466_; lean_object* v___x_3467_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = lean_unsigned_to_nat(0u);
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_box(0);
lean_inc_ref(v___y_3425_);
lean_inc_ref(v_params_3424_);
lean_inc(v_levels_3423_);
lean_inc(v_name_3442_);
lean_inc(v_numParams_3440_);
v___f_3457_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3457_, 0, v_numParams_3440_);
lean_closure_set(v___f_3457_, 1, v_name_3442_);
lean_closure_set(v___f_3457_, 2, v_levels_3423_);
lean_closure_set(v___f_3457_, 3, v_params_3424_);
lean_closure_set(v___f_3457_, 4, v___y_3425_);
lean_closure_set(v___f_3457_, 5, v___x_3454_);
v___x_3458_ = lean_replace_expr(v___f_3457_, v_a_3451_);
lean_dec(v_a_3451_);
lean_dec_ref(v___f_3457_);
lean_inc(v_name_3442_);
v___x_3459_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3442_);
v___x_3460_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__10___closed__1));
lean_inc(v___x_3459_);
v___x_3461_ = l_Lean_Name_append(v___x_3459_, v___x_3460_);
lean_inc(v_levels_3423_);
v___x_3462_ = l_Lean_mkConst(v___x_3461_, v_levels_3423_);
v___x_3463_ = lean_unsigned_to_nat(1u);
v___x_3464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3458_);
lean_inc_ref(v_params_3424_);
lean_inc(v_numIndices_3441_);
v___f_3465_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 20, 13);
lean_closure_set(v___f_3465_, 0, v___x_3463_);
lean_closure_set(v___f_3465_, 1, v_a_3453_);
lean_closure_set(v___f_3465_, 2, v_numIndices_3441_);
lean_closure_set(v___f_3465_, 3, v___x_3454_);
lean_closure_set(v___f_3465_, 4, v___x_3455_);
lean_closure_set(v___f_3465_, 5, v___x_3462_);
lean_closure_set(v___f_3465_, 6, v___x_3449_);
lean_closure_set(v___f_3465_, 7, v_params_3424_);
lean_closure_set(v___f_3465_, 8, v___x_3458_);
lean_closure_set(v___f_3465_, 9, v_a_3445_);
lean_closure_set(v___f_3465_, 10, v___x_3459_);
lean_closure_set(v___f_3465_, 11, v___x_3464_);
lean_closure_set(v___f_3465_, 12, v___x_3456_);
v___x_3466_ = 0;
v___x_3467_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v___x_3458_, v___x_3464_, v___f_3465_, v___x_3466_, v___x_3466_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
if (lean_obj_tag(v___x_3467_) == 0)
{
size_t v___x_3468_; size_t v___x_3469_; 
lean_dec_ref(v___x_3467_);
v___x_3468_ = ((size_t)1ULL);
v___x_3469_ = lean_usize_add(v_i_3429_, v___x_3468_);
v_i_3429_ = v___x_3469_;
v_b_3430_ = v___x_3456_;
goto _start;
}
else
{
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_params_3424_);
lean_dec(v_levels_3423_);
return v___x_3467_;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_dec(v_a_3451_);
lean_dec_ref(v___x_3449_);
lean_dec(v_a_3445_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_params_3424_);
lean_dec(v_levels_3423_);
v_a_3471_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3452_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3452_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v___x_3449_);
lean_dec(v_a_3445_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_params_3424_);
lean_dec(v_levels_3423_);
v_a_3479_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3450_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3450_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
else
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3494_; 
lean_dec(v_a_3445_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_params_3424_);
lean_dec(v_levels_3423_);
v_a_3487_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3489_ = v___x_3446_;
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3446_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3494_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3492_; 
if (v_isShared_3490_ == 0)
{
v___x_3492_ = v___x_3489_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_a_3487_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec(v___x_3443_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_params_3424_);
lean_dec(v_levels_3423_);
v_a_3495_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3444_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3444_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v_levels_3503_, lean_object* v_params_3504_, lean_object* v___y_3505_, lean_object* v_predicates_3506_, lean_object* v_as_3507_, lean_object* v_sz_3508_, lean_object* v_i_3509_, lean_object* v_b_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
size_t v_sz_boxed_3516_; size_t v_i_boxed_3517_; lean_object* v_res_3518_; 
v_sz_boxed_3516_ = lean_unbox_usize(v_sz_3508_);
lean_dec(v_sz_3508_);
v_i_boxed_3517_ = lean_unbox_usize(v_i_3509_);
lean_dec(v_i_3509_);
v_res_3518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3503_, v_params_3504_, v___y_3505_, v_predicates_3506_, v_as_3507_, v_sz_boxed_3516_, v_i_boxed_3517_, v_b_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v_as_3507_);
lean_dec_ref(v_predicates_3506_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3519_, size_t v_sz_3520_, size_t v_i_3521_, lean_object* v_bs_3522_){
_start:
{
uint8_t v___x_3523_; 
v___x_3523_ = lean_usize_dec_lt(v_i_3521_, v_sz_3520_);
if (v___x_3523_ == 0)
{
lean_dec(v_levels_3519_);
return v_bs_3522_;
}
else
{
lean_object* v_v_3524_; lean_object* v_toConstantVal_3525_; lean_object* v_name_3526_; lean_object* v___x_3527_; lean_object* v_bs_x27_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; size_t v___x_3531_; size_t v___x_3532_; lean_object* v___x_3533_; 
v_v_3524_ = lean_array_uget_borrowed(v_bs_3522_, v_i_3521_);
v_toConstantVal_3525_ = lean_ctor_get(v_v_3524_, 0);
v_name_3526_ = lean_ctor_get(v_toConstantVal_3525_, 0);
lean_inc(v_name_3526_);
v___x_3527_ = lean_unsigned_to_nat(0u);
v_bs_x27_3528_ = lean_array_uset(v_bs_3522_, v_i_3521_, v___x_3527_);
v___x_3529_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3526_);
lean_inc(v_levels_3519_);
v___x_3530_ = l_Lean_mkConst(v___x_3529_, v_levels_3519_);
v___x_3531_ = ((size_t)1ULL);
v___x_3532_ = lean_usize_add(v_i_3521_, v___x_3531_);
v___x_3533_ = lean_array_uset(v_bs_x27_3528_, v_i_3521_, v___x_3530_);
v_i_3521_ = v___x_3532_;
v_bs_3522_ = v___x_3533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3535_, lean_object* v_sz_3536_, lean_object* v_i_3537_, lean_object* v_bs_3538_){
_start:
{
size_t v_sz_boxed_3539_; size_t v_i_boxed_3540_; lean_object* v_res_3541_; 
v_sz_boxed_3539_ = lean_unbox_usize(v_sz_3536_);
lean_dec(v_sz_3536_);
v_i_boxed_3540_ = lean_unbox_usize(v_i_3537_);
lean_dec(v_i_3537_);
v_res_3541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3535_, v_sz_boxed_3539_, v_i_boxed_3540_, v_bs_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3542_, lean_object* v_levels_3543_, lean_object* v___y_3544_, lean_object* v_params_3545_, lean_object* v_x_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
size_t v_sz_3552_; size_t v___x_3553_; lean_object* v_predicates_3554_; size_t v_sz_3555_; lean_object* v_predicates_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
v_sz_3552_ = lean_array_size(v_infos_3542_);
v___x_3553_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3542_);
lean_inc(v_levels_3543_);
v_predicates_3554_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3543_, v_sz_3552_, v___x_3553_, v_infos_3542_);
v_sz_3555_ = lean_array_size(v_predicates_3554_);
v_predicates_3556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3545_, v_sz_3555_, v___x_3553_, v_predicates_3554_);
v___x_3557_ = lean_box(0);
v___x_3558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3543_, v_params_3545_, v___y_3544_, v_predicates_3556_, v_infos_3542_, v_sz_3552_, v___x_3553_, v___x_3557_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
lean_dec_ref(v_infos_3542_);
lean_dec_ref(v_predicates_3556_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v___x_3558_, 0);
lean_dec(v_unused_3566_);
v___x_3560_ = v___x_3558_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v___x_3558_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v___x_3557_);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3557_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
else
{
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3567_, lean_object* v_levels_3568_, lean_object* v___y_3569_, lean_object* v_params_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_res_3577_; 
v_res_3577_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3567_, v_levels_3568_, v___y_3569_, v_params_3570_, v_x_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v_x_3571_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3578_, size_t v_i_3579_, size_t v_stop_3580_, lean_object* v_b_3581_){
_start:
{
uint8_t v___x_3582_; 
v___x_3582_ = lean_usize_dec_eq(v_i_3579_, v_stop_3580_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; lean_object* v_ctors_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; size_t v___x_3587_; size_t v___x_3588_; 
v___x_3583_ = lean_array_uget_borrowed(v_as_3578_, v_i_3579_);
v_ctors_3584_ = lean_ctor_get(v___x_3583_, 4);
lean_inc(v_ctors_3584_);
v___x_3585_ = lean_array_mk(v_ctors_3584_);
v___x_3586_ = l_Array_append___redArg(v_b_3581_, v___x_3585_);
lean_dec_ref(v___x_3585_);
v___x_3587_ = ((size_t)1ULL);
v___x_3588_ = lean_usize_add(v_i_3579_, v___x_3587_);
v_i_3579_ = v___x_3588_;
v_b_3581_ = v___x_3586_;
goto _start;
}
else
{
return v_b_3581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3590_, lean_object* v_i_3591_, lean_object* v_stop_3592_, lean_object* v_b_3593_){
_start:
{
size_t v_i_boxed_3594_; size_t v_stop_boxed_3595_; lean_object* v_res_3596_; 
v_i_boxed_3594_ = lean_unbox_usize(v_i_3591_);
lean_dec(v_i_3591_);
v_stop_boxed_3595_ = lean_unbox_usize(v_stop_3592_);
lean_dec(v_stop_3592_);
v_res_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3590_, v_i_boxed_3594_, v_stop_boxed_3595_, v_b_3593_);
lean_dec_ref(v_as_3590_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v_toConstantVal_3608_; lean_object* v_numParams_3609_; lean_object* v_levelParams_3610_; lean_object* v_type_3611_; lean_object* v___x_3612_; lean_object* v_levels_3613_; lean_object* v___y_3615_; lean_object* v___x_3622_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
v___x_3605_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3606_ = lean_unsigned_to_nat(0u);
v___x_3607_ = lean_array_get_borrowed(v___x_3605_, v_infos_3599_, v___x_3606_);
v_toConstantVal_3608_ = lean_ctor_get(v___x_3607_, 0);
v_numParams_3609_ = lean_ctor_get(v___x_3607_, 1);
lean_inc(v_numParams_3609_);
v_levelParams_3610_ = lean_ctor_get(v_toConstantVal_3608_, 1);
v_type_3611_ = lean_ctor_get(v_toConstantVal_3608_, 2);
lean_inc_ref(v_type_3611_);
v___x_3612_ = lean_box(0);
lean_inc(v_levelParams_3610_);
v_levels_3613_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3610_, v___x_3612_);
v___x_3622_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3623_ = lean_array_get_size(v_infos_3599_);
v___x_3624_ = lean_nat_dec_lt(v___x_3606_, v___x_3623_);
if (v___x_3624_ == 0)
{
v___y_3615_ = v___x_3622_;
goto v___jp_3614_;
}
else
{
uint8_t v___x_3625_; 
v___x_3625_ = lean_nat_dec_le(v___x_3623_, v___x_3623_);
if (v___x_3625_ == 0)
{
if (v___x_3624_ == 0)
{
v___y_3615_ = v___x_3622_;
goto v___jp_3614_;
}
else
{
size_t v___x_3626_; size_t v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = ((size_t)0ULL);
v___x_3627_ = lean_usize_of_nat(v___x_3623_);
v___x_3628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3599_, v___x_3626_, v___x_3627_, v___x_3622_);
v___y_3615_ = v___x_3628_;
goto v___jp_3614_;
}
}
else
{
size_t v___x_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v___x_3629_ = ((size_t)0ULL);
v___x_3630_ = lean_usize_of_nat(v___x_3623_);
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3599_, v___x_3629_, v___x_3630_, v___x_3622_);
v___y_3615_ = v___x_3631_;
goto v___jp_3614_;
}
}
v___jp_3614_:
{
lean_object* v___f_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; 
lean_inc_ref(v_infos_3599_);
v___f_3616_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3616_, 0, v_infos_3599_);
lean_closure_set(v___f_3616_, 1, v_levels_3613_);
lean_closure_set(v___f_3616_, 2, v___y_3615_);
v___x_3617_ = lean_array_get_size(v_infos_3599_);
lean_dec_ref(v_infos_3599_);
v___x_3618_ = lean_nat_sub(v_numParams_3609_, v___x_3617_);
lean_dec(v_numParams_3609_);
v___x_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
v___x_3620_ = 0;
v___x_3621_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_type_3611_, v___x_3619_, v___f_3616_, v___x_3620_, v___x_3620_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
return v___x_3621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3639_, lean_object* v_constName_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3647_, lean_object* v_constName_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3647_, v_constName_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3655_, lean_object* v_ref_3656_, lean_object* v_constName_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3656_, v_constName_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3664_, lean_object* v_ref_3665_, lean_object* v_constName_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v_res_3672_; 
v_res_3672_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3664_, v_ref_3665_, v_constName_3666_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v_ref_3665_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3673_, lean_object* v_ref_3674_, lean_object* v_msg_3675_, lean_object* v_declHint_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; 
v___x_3682_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3674_, v_msg_3675_, v_declHint_3676_, v___y_3677_, v___y_3678_, v___y_3679_, v___y_3680_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3683_, lean_object* v_ref_3684_, lean_object* v_msg_3685_, lean_object* v_declHint_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3683_, v_ref_3684_, v_msg_3685_, v_declHint_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v_ref_3684_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3693_, lean_object* v_declHint_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3693_, v_declHint_3694_, v___y_3698_);
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3701_, lean_object* v_declHint_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3701_, v_declHint_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3709_, lean_object* v_ref_3710_, lean_object* v_msg_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3710_, v_msg_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3718_, lean_object* v_ref_3719_, lean_object* v_msg_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3718_, v_ref_3719_, v_msg_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v_ref_3719_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3730_, lean_object* v___x_3731_, lean_object* v_params_3732_, size_t v_sz_3733_, size_t v_i_3734_, lean_object* v_bs_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
uint8_t v___x_3741_; 
v___x_3741_ = lean_usize_dec_lt(v_i_3734_, v_sz_3733_);
if (v___x_3741_ == 0)
{
lean_object* v___x_3742_; 
lean_dec_ref(v_params_3732_);
lean_dec_ref(v___x_3731_);
lean_dec(v___x_3730_);
v___x_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3742_, 0, v_bs_3735_);
return v___x_3742_;
}
else
{
lean_object* v_v_3743_; lean_object* v_toConstantVal_3744_; lean_object* v_name_3745_; lean_object* v___x_3746_; lean_object* v_bs_x27_3747_; lean_object* v___y_3749_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v_v_3743_ = lean_array_uget_borrowed(v_bs_3735_, v_i_3734_);
v_toConstantVal_3744_ = lean_ctor_get(v_v_3743_, 0);
v_name_3745_ = lean_ctor_get(v_toConstantVal_3744_, 0);
lean_inc(v_name_3745_);
v___x_3746_ = lean_unsigned_to_nat(0u);
v_bs_x27_3747_ = lean_array_uset(v_bs_3735_, v_i_3734_, v___x_3746_);
v___x_3763_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3764_ = l_Lean_Name_append(v_name_3745_, v___x_3763_);
lean_inc(v___x_3730_);
v___x_3765_ = l_Lean_mkConst(v___x_3764_, v___x_3730_);
v___x_3766_ = l_Lean_Meta_unfoldDefinition(v___x_3765_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; size_t v_sz_3768_; size_t v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; uint8_t v___x_3774_; lean_object* v___x_3775_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref(v___x_3766_);
v_sz_3768_ = lean_array_size(v___x_3731_);
v___x_3769_ = ((size_t)0ULL);
lean_inc_ref(v___x_3731_);
v___x_3770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3732_, v_sz_3768_, v___x_3769_, v___x_3731_);
lean_inc_ref(v_params_3732_);
v___x_3771_ = l_Array_append___redArg(v_params_3732_, v___x_3770_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = l_Lean_mkAppN(v_a_3767_, v___x_3771_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = 0;
v___x_3774_ = 1;
v___x_3775_ = l_Lean_Meta_mkLambdaFVars(v_params_3732_, v___x_3772_, v___x_3773_, v___x_3741_, v___x_3773_, v___x_3741_, v___x_3774_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
v___y_3749_ = v___x_3775_;
goto v___jp_3748_;
}
else
{
v___y_3749_ = v___x_3766_;
goto v___jp_3748_;
}
v___jp_3748_:
{
if (lean_obj_tag(v___y_3749_) == 0)
{
lean_object* v_a_3750_; size_t v___x_3751_; size_t v___x_3752_; lean_object* v___x_3753_; 
v_a_3750_ = lean_ctor_get(v___y_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref(v___y_3749_);
v___x_3751_ = ((size_t)1ULL);
v___x_3752_ = lean_usize_add(v_i_3734_, v___x_3751_);
v___x_3753_ = lean_array_uset(v_bs_x27_3747_, v_i_3734_, v_a_3750_);
v_i_3734_ = v___x_3752_;
v_bs_3735_ = v___x_3753_;
goto _start;
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v_bs_x27_3747_);
lean_dec_ref(v_params_3732_);
lean_dec_ref(v___x_3731_);
lean_dec(v___x_3730_);
v_a_3755_ = lean_ctor_get(v___y_3749_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___y_3749_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___y_3749_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___y_3749_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3776_, lean_object* v___x_3777_, lean_object* v_params_3778_, lean_object* v_sz_3779_, lean_object* v_i_3780_, lean_object* v_bs_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
size_t v_sz_boxed_3787_; size_t v_i_boxed_3788_; lean_object* v_res_3789_; 
v_sz_boxed_3787_ = lean_unbox_usize(v_sz_3779_);
lean_dec(v_sz_3779_);
v_i_boxed_3788_ = lean_unbox_usize(v_i_3780_);
lean_dec(v_i_3780_);
v_res_3789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3776_, v___x_3777_, v_params_3778_, v_sz_boxed_3787_, v_i_boxed_3788_, v_bs_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3790_, lean_object* v___x_3791_, size_t v_sz_3792_, size_t v___x_3793_, lean_object* v_a_3794_, lean_object* v_params_3795_, lean_object* v_x_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3790_, v___x_3791_, v_params_3795_, v_sz_3792_, v___x_3793_, v_a_3794_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3805_, lean_object* v___x_3806_, lean_object* v_sz_3807_, lean_object* v___x_3808_, lean_object* v_a_3809_, lean_object* v_params_3810_, lean_object* v_x_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_){
_start:
{
size_t v_sz_boxed_3819_; size_t v___x_4581__boxed_3820_; lean_object* v_res_3821_; 
v_sz_boxed_3819_ = lean_unbox_usize(v_sz_3807_);
lean_dec(v_sz_3807_);
v___x_4581__boxed_3820_ = lean_unbox_usize(v___x_3808_);
lean_dec(v___x_3808_);
v_res_3821_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3805_, v___x_3806_, v_sz_boxed_3819_, v___x_4581__boxed_3820_, v_a_3809_, v_params_3810_, v_x_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec_ref(v_x_3811_);
return v_res_3821_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0));
v___x_3824_ = l_Lean_stringToMessageData(v___x_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object* v_constName_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; lean_object* v_env_3834_; lean_object* v___x_3835_; 
v___x_3833_ = lean_st_ref_get(v___y_3831_);
v_env_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc_ref(v_env_3834_);
lean_dec(v___x_3833_);
lean_inc(v_constName_3825_);
v___x_3835_ = l_Lean_isInductiveCore_x3f(v_env_3834_, v_constName_3825_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v___x_3836_; uint8_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3836_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_3837_ = 0;
v___x_3838_ = l_Lean_MessageData_ofConstName(v_constName_3825_, v___x_3837_);
v___x_3839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3836_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___x_3840_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
v___x_3841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3839_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
lean_inc_ref(v___y_3826_);
v___x_3842_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_3841_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
return v___x_3842_;
}
else
{
lean_object* v_val_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_constName_3825_);
v_val_3843_ = lean_ctor_get(v___x_3835_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3835_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3835_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_val_3843_);
lean_dec(v___x_3835_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
if (v_isShared_3846_ == 0)
{
lean_ctor_set_tag(v___x_3845_, 0);
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_val_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
return v___x_3848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object* v_constName_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t v_sz_3860_, size_t v_i_3861_, lean_object* v_bs_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
uint8_t v___x_3870_; 
v___x_3870_ = lean_usize_dec_lt(v_i_3861_, v_sz_3860_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3871_, 0, v_bs_3862_);
return v___x_3871_;
}
else
{
lean_object* v_v_3872_; lean_object* v_declName_3873_; lean_object* v___x_3874_; 
v_v_3872_ = lean_array_uget_borrowed(v_bs_3862_, v_i_3861_);
v_declName_3873_ = lean_ctor_get(v_v_3872_, 1);
lean_inc(v_declName_3873_);
v___x_3874_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_3873_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; lean_object* v_bs_x27_3877_; size_t v___x_3878_; size_t v___x_3879_; lean_object* v___x_3880_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
v___x_3876_ = lean_unsigned_to_nat(0u);
v_bs_x27_3877_ = lean_array_uset(v_bs_3862_, v_i_3861_, v___x_3876_);
v___x_3878_ = ((size_t)1ULL);
v___x_3879_ = lean_usize_add(v_i_3861_, v___x_3878_);
v___x_3880_ = lean_array_uset(v_bs_x27_3877_, v_i_3861_, v_a_3875_);
v_i_3861_ = v___x_3879_;
v_bs_3862_ = v___x_3880_;
goto _start;
}
else
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3889_; 
lean_dec_ref(v_bs_3862_);
v_a_3882_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3889_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3889_ == 0)
{
v___x_3884_ = v___x_3874_;
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3874_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3889_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
lean_object* v___x_3887_; 
if (v_isShared_3885_ == 0)
{
v___x_3887_ = v___x_3884_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_a_3882_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object* v_sz_3890_, lean_object* v_i_3891_, lean_object* v_bs_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
size_t v_sz_boxed_3900_; size_t v_i_boxed_3901_; lean_object* v_res_3902_; 
v_sz_boxed_3900_ = lean_unbox_usize(v_sz_3890_);
lean_dec(v_sz_3890_);
v_i_boxed_3901_ = lean_unbox_usize(v_i_3891_);
lean_dec(v_i_3891_);
v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_3900_, v_i_boxed_3901_, v_bs_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
return v_res_3902_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3903_ = l_Lean_instInhabitedExpr;
v___x_3904_ = lean_box(0);
v___x_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
lean_ctor_set(v___x_3905_, 1, v___x_3903_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3906_, lean_object* v_a_3907_, lean_object* v___x_3908_, lean_object* v_as_3909_, lean_object* v_i_3910_, lean_object* v_j_3911_, lean_object* v_bs_3912_){
_start:
{
lean_object* v_zero_3913_; uint8_t v_isZero_3914_; 
v_zero_3913_ = lean_unsigned_to_nat(0u);
v_isZero_3914_ = lean_nat_dec_eq(v_i_3910_, v_zero_3913_);
if (v_isZero_3914_ == 1)
{
lean_dec(v_j_3911_);
lean_dec(v_i_3910_);
lean_dec(v___x_3908_);
return v_bs_3912_;
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v_ref_3917_; lean_object* v_modifiers_3918_; uint8_t v_isGreatest_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v_fst_3922_; lean_object* v_snd_3923_; lean_object* v_one_3924_; lean_object* v_n_3925_; lean_object* v___x_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; uint8_t v___y_3930_; 
v___x_3915_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v___x_3916_ = lean_array_get_borrowed(v___x_3915_, v_coinductiveElabData_3906_, v_j_3911_);
v_ref_3917_ = lean_ctor_get(v___x_3916_, 2);
v_modifiers_3918_ = lean_ctor_get(v___x_3916_, 3);
v_isGreatest_3919_ = lean_ctor_get_uint8(v___x_3916_, sizeof(void*)*5);
v___x_3920_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3921_ = lean_array_get_borrowed(v___x_3920_, v_a_3907_, v_j_3911_);
v_fst_3922_ = lean_ctor_get(v___x_3921_, 0);
v_snd_3923_ = lean_ctor_get(v___x_3921_, 1);
v_one_3924_ = lean_unsigned_to_nat(1u);
v_n_3925_ = lean_nat_sub(v_i_3910_, v_one_3924_);
lean_dec(v_i_3910_);
v___x_3926_ = lean_array_fget_borrowed(v_as_3909_, v_j_3911_);
v___x_3927_ = 0;
v___x_3928_ = lean_box(0);
if (v_isGreatest_3919_ == 0)
{
uint8_t v___x_3938_; 
v___x_3938_ = 2;
v___y_3930_ = v___x_3938_;
goto v___jp_3929_;
}
else
{
uint8_t v___x_3939_; 
v___x_3939_ = 1;
v___y_3930_ = v___x_3939_;
goto v___jp_3929_;
}
v___jp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_inc(v_ref_3917_);
v___x_3931_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3931_, 0, v_ref_3917_);
lean_ctor_set(v___x_3931_, 1, v___x_3928_);
lean_ctor_set_uint8(v___x_3931_, sizeof(void*)*2, v___y_3930_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
lean_inc(v_ref_3917_);
v___x_3933_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3933_, 0, v_ref_3917_);
lean_ctor_set(v___x_3933_, 1, v___x_3928_);
lean_ctor_set(v___x_3933_, 2, v___x_3928_);
lean_ctor_set(v___x_3933_, 3, v___x_3932_);
lean_ctor_set(v___x_3933_, 4, v___x_3928_);
lean_ctor_set(v___x_3933_, 5, v_zero_3913_);
lean_inc(v___x_3926_);
lean_inc(v_snd_3923_);
lean_inc(v_fst_3922_);
lean_inc_ref(v_modifiers_3918_);
lean_inc(v___x_3908_);
lean_inc_n(v_ref_3917_, 2);
v___x_3934_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3934_, 0, v_ref_3917_);
lean_ctor_set(v___x_3934_, 1, v___x_3908_);
lean_ctor_set(v___x_3934_, 2, v_modifiers_3918_);
lean_ctor_set(v___x_3934_, 3, v_fst_3922_);
lean_ctor_set(v___x_3934_, 4, v_ref_3917_);
lean_ctor_set(v___x_3934_, 5, v_zero_3913_);
lean_ctor_set(v___x_3934_, 6, v_snd_3923_);
lean_ctor_set(v___x_3934_, 7, v___x_3926_);
lean_ctor_set(v___x_3934_, 8, v___x_3933_);
lean_ctor_set_uint8(v___x_3934_, sizeof(void*)*9, v___x_3927_);
v___x_3935_ = lean_nat_add(v_j_3911_, v_one_3924_);
lean_dec(v_j_3911_);
v___x_3936_ = lean_array_push(v_bs_3912_, v___x_3934_);
v_i_3910_ = v_n_3925_;
v_j_3911_ = v___x_3935_;
v_bs_3912_ = v___x_3936_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object* v_coinductiveElabData_3940_, lean_object* v_a_3941_, lean_object* v___x_3942_, lean_object* v_as_3943_, lean_object* v_i_3944_, lean_object* v_j_3945_, lean_object* v_bs_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_3940_, v_a_3941_, v___x_3942_, v_as_3943_, v_i_3944_, v_j_3945_, v_bs_3946_);
lean_dec_ref(v_as_3943_);
lean_dec_ref(v_a_3941_);
lean_dec_ref(v_coinductiveElabData_3940_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
if (lean_obj_tag(v_a_3948_) == 0)
{
lean_object* v___x_3950_; 
v___x_3950_ = l_List_reverse___redArg(v_a_3949_);
return v___x_3950_;
}
else
{
lean_object* v_head_3951_; lean_object* v_tail_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3961_; 
v_head_3951_ = lean_ctor_get(v_a_3948_, 0);
v_tail_3952_ = lean_ctor_get(v_a_3948_, 1);
v_isSharedCheck_3961_ = !lean_is_exclusive(v_a_3948_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3954_ = v_a_3948_;
v_isShared_3955_ = v_isSharedCheck_3961_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_tail_3952_);
lean_inc(v_head_3951_);
lean_dec(v_a_3948_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3961_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3958_; 
v___x_3956_ = l_Lean_MessageData_ofName(v_head_3951_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 1, v_a_3949_);
lean_ctor_set(v___x_3954_, 0, v___x_3956_);
v___x_3958_ = v___x_3954_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v_a_3949_);
v___x_3958_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
v_a_3948_ = v_tail_3952_;
v_a_3949_ = v___x_3958_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t v_sz_3962_, size_t v_i_3963_, lean_object* v_bs_3964_){
_start:
{
uint8_t v___x_3965_; 
v___x_3965_ = lean_usize_dec_lt(v_i_3963_, v_sz_3962_);
if (v___x_3965_ == 0)
{
return v_bs_3964_;
}
else
{
lean_object* v_v_3966_; lean_object* v_declName_3967_; lean_object* v___x_3968_; lean_object* v_bs_x27_3969_; size_t v___x_3970_; size_t v___x_3971_; lean_object* v___x_3972_; 
v_v_3966_ = lean_array_uget_borrowed(v_bs_3964_, v_i_3963_);
v_declName_3967_ = lean_ctor_get(v_v_3966_, 1);
lean_inc(v_declName_3967_);
v___x_3968_ = lean_unsigned_to_nat(0u);
v_bs_x27_3969_ = lean_array_uset(v_bs_3964_, v_i_3963_, v___x_3968_);
v___x_3970_ = ((size_t)1ULL);
v___x_3971_ = lean_usize_add(v_i_3963_, v___x_3970_);
v___x_3972_ = lean_array_uset(v_bs_x27_3969_, v_i_3963_, v_declName_3967_);
v_i_3963_ = v___x_3971_;
v_bs_3964_ = v___x_3972_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object* v_sz_3974_, lean_object* v_i_3975_, lean_object* v_bs_3976_){
_start:
{
size_t v_sz_boxed_3977_; size_t v_i_boxed_3978_; lean_object* v_res_3979_; 
v_sz_boxed_3977_ = lean_unbox_usize(v_sz_3974_);
lean_dec(v_sz_3974_);
v_i_boxed_3978_ = lean_unbox_usize(v_i_3975_);
lean_dec(v_i_3975_);
v_res_3979_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_3977_, v_i_boxed_3978_, v_bs_3976_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v_v_3980_, lean_object* v___x_3981_, lean_object* v___x_3982_, uint8_t v___x_3983_, lean_object* v_args_3984_, lean_object* v_body_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v_numParams_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; 
v_numParams_3993_ = lean_ctor_get(v_v_3980_, 1);
lean_inc(v_numParams_3993_);
lean_dec(v_v_3980_);
lean_inc_ref(v_args_3984_);
v___x_3994_ = l_Array_toSubarray___redArg(v_args_3984_, v___x_3981_, v___x_3982_);
v___x_3995_ = l_Subarray_copy___redArg(v___x_3994_);
v___x_3996_ = lean_array_get_size(v_args_3984_);
v___x_3997_ = l_Array_toSubarray___redArg(v_args_3984_, v_numParams_3993_, v___x_3996_);
v___x_3998_ = l_Subarray_copy___redArg(v___x_3997_);
v___x_3999_ = l_Array_append___redArg(v___x_3995_, v___x_3998_);
lean_dec_ref(v___x_3998_);
v___x_4000_ = 0;
v___x_4001_ = 1;
v___x_4002_ = l_Lean_Meta_mkForallFVars(v___x_3999_, v_body_3985_, v___x_4000_, v___x_3983_, v___x_3983_, v___x_4001_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec_ref(v___x_3999_);
return v___x_4002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v_v_4003_, lean_object* v___x_4004_, lean_object* v___x_4005_, lean_object* v___x_4006_, lean_object* v_args_4007_, lean_object* v_body_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
uint8_t v___x_4834__boxed_4016_; lean_object* v_res_4017_; 
v___x_4834__boxed_4016_ = lean_unbox(v___x_4006_);
v_res_4017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_4003_, v___x_4004_, v___x_4005_, v___x_4834__boxed_4016_, v_args_4007_, v_body_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_4018_, size_t v_sz_4019_, size_t v_i_4020_, lean_object* v_bs_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
uint8_t v___x_4029_; 
v___x_4029_ = lean_usize_dec_lt(v_i_4020_, v_sz_4019_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; 
lean_dec(v___x_4018_);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v_bs_4021_);
return v___x_4030_;
}
else
{
lean_object* v_v_4031_; lean_object* v_toConstantVal_4032_; lean_object* v_name_4033_; lean_object* v_type_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___f_4037_; uint8_t v___x_4038_; lean_object* v___x_4039_; 
v_v_4031_ = lean_array_uget_borrowed(v_bs_4021_, v_i_4020_);
v_toConstantVal_4032_ = lean_ctor_get(v_v_4031_, 0);
v_name_4033_ = lean_ctor_get(v_toConstantVal_4032_, 0);
lean_inc(v_name_4033_);
v_type_4034_ = lean_ctor_get(v_toConstantVal_4032_, 2);
v___x_4035_ = lean_unsigned_to_nat(0u);
v___x_4036_ = lean_box(v___x_4029_);
lean_inc(v___x_4018_);
lean_inc(v_v_4031_);
v___f_4037_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4037_, 0, v_v_4031_);
lean_closure_set(v___f_4037_, 1, v___x_4035_);
lean_closure_set(v___f_4037_, 2, v___x_4018_);
lean_closure_set(v___f_4037_, 3, v___x_4036_);
v___x_4038_ = 0;
lean_inc_ref(v_type_4034_);
v___x_4039_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_type_4034_, v___f_4037_, v___x_4038_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v_bs_x27_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; size_t v___x_4044_; size_t v___x_4045_; lean_object* v___x_4046_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
v_bs_x27_4041_ = lean_array_uset(v_bs_4021_, v_i_4020_, v___x_4035_);
v___x_4042_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4033_);
v___x_4043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
lean_ctor_set(v___x_4043_, 1, v_a_4040_);
v___x_4044_ = ((size_t)1ULL);
v___x_4045_ = lean_usize_add(v_i_4020_, v___x_4044_);
v___x_4046_ = lean_array_uset(v_bs_x27_4041_, v_i_4020_, v___x_4043_);
v_i_4020_ = v___x_4045_;
v_bs_4021_ = v___x_4046_;
goto _start;
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v_name_4033_);
lean_dec_ref(v_bs_4021_);
lean_dec(v___x_4018_);
v_a_4048_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4039_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4039_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object* v___x_4056_, lean_object* v_sz_4057_, lean_object* v_i_4058_, lean_object* v_bs_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
size_t v_sz_boxed_4067_; size_t v_i_boxed_4068_; lean_object* v_res_4069_; 
v_sz_boxed_4067_ = lean_unbox_usize(v_sz_4057_);
lean_dec(v_sz_4057_);
v_i_boxed_4068_ = lean_unbox_usize(v_i_4058_);
lean_dec(v_i_4058_);
v_res_4069_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4056_, v_sz_boxed_4067_, v_i_boxed_4068_, v_bs_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object* v___x_4070_, size_t v_sz_4071_, size_t v_i_4072_, lean_object* v_bs_4073_){
_start:
{
uint8_t v___x_4074_; 
v___x_4074_ = lean_usize_dec_lt(v_i_4072_, v_sz_4071_);
if (v___x_4074_ == 0)
{
lean_dec(v___x_4070_);
return v_bs_4073_;
}
else
{
lean_object* v_v_4075_; lean_object* v_fst_4076_; lean_object* v___x_4077_; lean_object* v_bs_x27_4078_; lean_object* v___x_4079_; size_t v___x_4080_; size_t v___x_4081_; lean_object* v___x_4082_; 
v_v_4075_ = lean_array_uget_borrowed(v_bs_4073_, v_i_4072_);
v_fst_4076_ = lean_ctor_get(v_v_4075_, 0);
lean_inc(v_fst_4076_);
v___x_4077_ = lean_unsigned_to_nat(0u);
v_bs_x27_4078_ = lean_array_uset(v_bs_4073_, v_i_4072_, v___x_4077_);
lean_inc(v___x_4070_);
v___x_4079_ = l_Lean_mkConst(v_fst_4076_, v___x_4070_);
v___x_4080_ = ((size_t)1ULL);
v___x_4081_ = lean_usize_add(v_i_4072_, v___x_4080_);
v___x_4082_ = lean_array_uset(v_bs_x27_4078_, v_i_4072_, v___x_4079_);
v_i_4072_ = v___x_4081_;
v_bs_4073_ = v___x_4082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object* v___x_4084_, lean_object* v_sz_4085_, lean_object* v_i_4086_, lean_object* v_bs_4087_){
_start:
{
size_t v_sz_boxed_4088_; size_t v_i_boxed_4089_; lean_object* v_res_4090_; 
v_sz_boxed_4088_ = lean_unbox_usize(v_sz_4085_);
lean_dec(v_sz_4085_);
v_i_boxed_4089_ = lean_unbox_usize(v_i_4086_);
lean_dec(v_i_4086_);
v_res_4090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4084_, v_sz_boxed_4088_, v_i_boxed_4089_, v_bs_4087_);
return v_res_4090_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCoinductive___closed__1(void){
_start:
{
lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4092_ = ((lean_object*)(l_Lean_Elab_Command_elabCoinductive___closed__0));
v___x_4093_ = l_Lean_stringToMessageData(v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object* v_coinductiveElabData_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_cls_4102_; lean_object* v___x_4103_; lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4198_; 
v_cls_4102_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4103_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_cls_4102_, v_a_4099_);
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4198_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4198_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4108_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; uint8_t v___x_4187_; 
v___x_4108_ = l_Lean_instInhabitedInductiveVal_default;
v___x_4187_ = lean_unbox(v_a_4104_);
lean_dec(v_a_4104_);
if (v___x_4187_ == 0)
{
v___y_4110_ = v_a_4095_;
v___y_4111_ = v_a_4096_;
v___y_4112_ = v_a_4097_;
v___y_4113_ = v_a_4098_;
v___y_4114_ = v_a_4099_;
v___y_4115_ = v_a_4100_;
goto v___jp_4109_;
}
else
{
lean_object* v___x_4188_; size_t v_sz_4189_; size_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4188_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4189_ = lean_array_size(v_coinductiveElabData_4094_);
v___x_4190_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4094_);
v___x_4191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4189_, v___x_4190_, v_coinductiveElabData_4094_);
v___x_4192_ = lean_array_to_list(v___x_4191_);
v___x_4193_ = lean_box(0);
v___x_4194_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4192_, v___x_4193_);
v___x_4195_ = l_Lean_MessageData_ofList(v___x_4194_);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4188_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_cls_4102_, v___x_4196_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_dec_ref(v___x_4197_);
v___y_4110_ = v_a_4095_;
v___y_4111_ = v_a_4096_;
v___y_4112_ = v_a_4097_;
v___y_4113_ = v_a_4098_;
v___y_4114_ = v_a_4099_;
v___y_4115_ = v_a_4100_;
goto v___jp_4109_;
}
else
{
lean_del_object(v___x_4106_);
lean_dec_ref(v_coinductiveElabData_4094_);
return v___x_4197_;
}
}
v___jp_4109_:
{
size_t v_sz_4116_; size_t v___x_4117_; lean_object* v___x_4118_; 
v_sz_4116_ = lean_array_size(v_coinductiveElabData_4094_);
v___x_4117_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4094_);
v___x_4118_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4116_, v___x_4117_, v_coinductiveElabData_4094_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v_toConstantVal_4122_; lean_object* v_numParams_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; size_t v_sz_4126_; lean_object* v___x_4127_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref(v___x_4118_);
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = lean_array_get_borrowed(v___x_4108_, v_a_4119_, v___x_4120_);
v_toConstantVal_4122_ = lean_ctor_get(v___x_4121_, 0);
v_numParams_4123_ = lean_ctor_get(v___x_4121_, 1);
v___x_4124_ = lean_array_get_size(v_a_4119_);
v___x_4125_ = lean_nat_sub(v_numParams_4123_, v___x_4124_);
v_sz_4126_ = lean_array_size(v_a_4119_);
lean_inc(v_a_4119_);
lean_inc(v___x_4125_);
v___x_4127_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4125_, v_sz_4126_, v___x_4117_, v_a_4119_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v_levelParams_4129_; lean_object* v_type_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; size_t v_sz_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___f_4137_; lean_object* v___x_4139_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref(v___x_4127_);
v_levelParams_4129_ = lean_ctor_get(v_toConstantVal_4122_, 1);
v_type_4130_ = lean_ctor_get(v_toConstantVal_4122_, 2);
v___x_4131_ = lean_box(0);
lean_inc(v_levelParams_4129_);
v___x_4132_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4129_, v___x_4131_);
v_sz_4133_ = lean_array_size(v_a_4128_);
lean_inc(v_a_4128_);
lean_inc(v___x_4132_);
v___x_4134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4132_, v_sz_4133_, v___x_4117_, v_a_4128_);
v___x_4135_ = lean_box_usize(v_sz_4126_);
v___x_4136_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4119_);
v___f_4137_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4137_, 0, v___x_4132_);
lean_closure_set(v___f_4137_, 1, v___x_4134_);
lean_closure_set(v___f_4137_, 2, v___x_4135_);
lean_closure_set(v___f_4137_, 3, v___x_4136_);
lean_closure_set(v___f_4137_, 4, v_a_4119_);
lean_inc(v___x_4125_);
if (v_isShared_4107_ == 0)
{
lean_ctor_set_tag(v___x_4106_, 1);
lean_ctor_set(v___x_4106_, 0, v___x_4125_);
v___x_4139_ = v___x_4106_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4125_);
v___x_4139_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
uint8_t v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = 0;
lean_inc_ref(v_type_4130_);
v___x_4141_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__9___redArg(v_type_4130_, v___x_4139_, v___f_4137_, v___x_4140_, v___x_4140_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v___x_4141_);
v___x_4143_ = l_Lean_Meta_getLocalInstances___redArg(v___y_4112_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v_lctx_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref(v___x_4143_);
v_lctx_4145_ = lean_ctor_get(v___y_4112_, 2);
v___x_4146_ = lean_array_get_size(v_a_4142_);
v___x_4147_ = lean_mk_empty_array_with_capacity(v___x_4146_);
lean_inc(v_levelParams_4129_);
v___x_4148_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4094_, v_a_4128_, v_levelParams_4129_, v_a_4142_, v___x_4146_, v___x_4120_, v___x_4147_);
lean_dec(v_a_4142_);
lean_dec(v_a_4128_);
lean_inc_ref(v_lctx_4145_);
v___x_4149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4149_, 0, v_lctx_4145_);
lean_ctor_set(v___x_4149_, 1, v_a_4144_);
v___x_4150_ = l_Lean_Elab_partialFixpoint(v___x_4149_, v___x_4148_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v___x_4151_; 
lean_dec_ref(v___x_4150_);
lean_inc(v_a_4119_);
v___x_4151_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4119_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v___x_4152_; 
lean_dec_ref(v___x_4151_);
lean_inc(v_a_4119_);
v___x_4152_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4125_, v_a_4119_, v_coinductiveElabData_4094_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v___x_4153_; 
lean_dec_ref(v___x_4152_);
v___x_4153_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4119_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4153_;
}
else
{
lean_dec(v_a_4119_);
return v___x_4152_;
}
}
else
{
lean_dec(v___x_4125_);
lean_dec(v_a_4119_);
lean_dec_ref(v_coinductiveElabData_4094_);
return v___x_4151_;
}
}
else
{
lean_dec(v___x_4125_);
lean_dec(v_a_4119_);
lean_dec_ref(v_coinductiveElabData_4094_);
return v___x_4150_;
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
lean_dec(v_a_4142_);
lean_dec(v_a_4128_);
lean_dec(v___x_4125_);
lean_dec(v_a_4119_);
lean_dec_ref(v_coinductiveElabData_4094_);
v_a_4154_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4143_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4143_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_a_4128_);
lean_dec(v___x_4125_);
lean_dec(v_a_4119_);
lean_dec_ref(v_coinductiveElabData_4094_);
v_a_4162_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4141_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4141_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
else
{
lean_object* v_a_4171_; lean_object* v___x_4173_; uint8_t v_isShared_4174_; uint8_t v_isSharedCheck_4178_; 
lean_dec(v___x_4125_);
lean_dec(v_a_4119_);
lean_del_object(v___x_4106_);
lean_dec_ref(v_coinductiveElabData_4094_);
v_a_4171_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4173_ = v___x_4127_;
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
else
{
lean_inc(v_a_4171_);
lean_dec(v___x_4127_);
v___x_4173_ = lean_box(0);
v_isShared_4174_ = v_isSharedCheck_4178_;
goto v_resetjp_4172_;
}
v_resetjp_4172_:
{
lean_object* v___x_4176_; 
if (v_isShared_4174_ == 0)
{
v___x_4176_ = v___x_4173_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4171_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_del_object(v___x_4106_);
lean_dec_ref(v_coinductiveElabData_4094_);
v_a_4179_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4118_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4118_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
lean_dec(v_a_4201_);
lean_dec_ref(v_a_4200_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4208_, lean_object* v___x_4209_, lean_object* v_params_4210_, size_t v_sz_4211_, size_t v_i_4212_, lean_object* v_bs_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4208_, v___x_4209_, v_params_4210_, v_sz_4211_, v_i_4212_, v_bs_4213_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4222_, lean_object* v___x_4223_, lean_object* v_params_4224_, lean_object* v_sz_4225_, lean_object* v_i_4226_, lean_object* v_bs_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
size_t v_sz_boxed_4235_; size_t v_i_boxed_4236_; lean_object* v_res_4237_; 
v_sz_boxed_4235_ = lean_unbox_usize(v_sz_4225_);
lean_dec(v_sz_4225_);
v_i_boxed_4236_ = lean_unbox_usize(v_i_4226_);
lean_dec(v_i_4226_);
v_res_4237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4222_, v___x_4223_, v_params_4224_, v_sz_boxed_4235_, v_i_boxed_4236_, v_bs_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4238_, lean_object* v_a_4239_, lean_object* v___x_4240_, lean_object* v_as_4241_, lean_object* v_i_4242_, lean_object* v_j_4243_, lean_object* v_inv_4244_, lean_object* v_bs_4245_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4238_, v_a_4239_, v___x_4240_, v_as_4241_, v_i_4242_, v_j_4243_, v_bs_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4247_, lean_object* v_a_4248_, lean_object* v___x_4249_, lean_object* v_as_4250_, lean_object* v_i_4251_, lean_object* v_j_4252_, lean_object* v_inv_4253_, lean_object* v_bs_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4247_, v_a_4248_, v___x_4249_, v_as_4250_, v_i_4251_, v_j_4252_, v_inv_4253_, v_bs_4254_);
lean_dec_ref(v_as_4250_);
lean_dec_ref(v_a_4248_);
lean_dec_ref(v_coinductiveElabData_4247_);
return v_res_4255_;
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
