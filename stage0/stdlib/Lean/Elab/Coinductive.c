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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0(void){
_start:
{
size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; 
v___x_396_ = ((size_t)5ULL);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_shift_left(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; 
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0);
v___x_401_ = lean_usize_sub(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(lean_object* v_x_403_, size_t v_x_404_, size_t v_x_405_, lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
lean_object* v_es_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v_j_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_es_408_ = lean_ctor_get(v_x_403_, 0);
v___x_409_ = ((size_t)5ULL);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__1);
v___x_412_ = lean_usize_land(v_x_404_, v___x_411_);
v_j_413_ = lean_usize_to_nat(v___x_412_);
v___x_414_ = lean_array_get_size(v_es_408_);
v___x_415_ = lean_nat_dec_lt(v_j_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec(v_j_413_);
lean_dec(v_x_407_);
lean_dec(v_x_406_);
return v_x_403_;
}
else
{
lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_452_; 
lean_inc_ref(v_es_408_);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v_x_403_, 0);
lean_dec(v_unused_453_);
v___x_417_ = v_x_403_;
v_isShared_418_ = v_isSharedCheck_452_;
goto v_resetjp_416_;
}
else
{
lean_dec(v_x_403_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_452_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_v_419_; lean_object* v___x_420_; lean_object* v_xs_x27_421_; lean_object* v___y_423_; 
v_v_419_ = lean_array_fget(v_es_408_, v_j_413_);
v___x_420_ = lean_box(0);
v_xs_x27_421_ = lean_array_fset(v_es_408_, v_j_413_, v___x_420_);
switch(lean_obj_tag(v_v_419_))
{
case 0:
{
lean_object* v_key_428_; lean_object* v_val_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_439_; 
v_key_428_ = lean_ctor_get(v_v_419_, 0);
v_val_429_ = lean_ctor_get(v_v_419_, 1);
v_isSharedCheck_439_ = !lean_is_exclusive(v_v_419_);
if (v_isSharedCheck_439_ == 0)
{
v___x_431_ = v_v_419_;
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_val_429_);
lean_inc(v_key_428_);
lean_dec(v_v_419_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_439_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
uint8_t v___x_433_; 
v___x_433_ = l_Lean_instBEqMVarId_beq(v_x_406_, v_key_428_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_del_object(v___x_431_);
v___x_434_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_428_, v_val_429_, v_x_406_, v_x_407_);
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
v___y_423_ = v___x_435_;
goto v___jp_422_;
}
else
{
lean_object* v___x_437_; 
lean_dec(v_val_429_);
lean_dec(v_key_428_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v_x_407_);
lean_ctor_set(v___x_431_, 0, v_x_406_);
v___x_437_ = v___x_431_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_x_406_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v_x_407_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
v___y_423_ = v___x_437_;
goto v___jp_422_;
}
}
}
}
case 1:
{
lean_object* v_node_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_450_; 
v_node_440_ = lean_ctor_get(v_v_419_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v_v_419_);
if (v_isSharedCheck_450_ == 0)
{
v___x_442_ = v_v_419_;
v_isShared_443_ = v_isSharedCheck_450_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_node_440_);
lean_dec(v_v_419_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_450_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_444_ = lean_usize_shift_right(v_x_404_, v___x_409_);
v___x_445_ = lean_usize_add(v_x_405_, v___x_410_);
v___x_446_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_node_440_, v___x_444_, v___x_445_, v_x_406_, v_x_407_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 0, v___x_446_);
v___x_448_ = v___x_442_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
v___y_423_ = v___x_448_;
goto v___jp_422_;
}
}
}
default: 
{
lean_object* v___x_451_; 
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v_x_406_);
lean_ctor_set(v___x_451_, 1, v_x_407_);
v___y_423_ = v___x_451_;
goto v___jp_422_;
}
}
v___jp_422_:
{
lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_424_ = lean_array_fset(v_xs_x27_421_, v_j_413_, v___y_423_);
lean_dec(v_j_413_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_424_);
v___x_426_ = v___x_417_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_ks_454_; lean_object* v_vs_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_475_; 
v_ks_454_ = lean_ctor_get(v_x_403_, 0);
v_vs_455_ = lean_ctor_get(v_x_403_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_403_);
if (v_isSharedCheck_475_ == 0)
{
v___x_457_ = v_x_403_;
v_isShared_458_ = v_isSharedCheck_475_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_vs_455_);
lean_inc(v_ks_454_);
lean_dec(v_x_403_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_475_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_ks_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_vs_455_);
v___x_460_ = v_reuseFailAlloc_474_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v_newNode_461_; uint8_t v___y_463_; size_t v___x_469_; uint8_t v___x_470_; 
v_newNode_461_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v___x_460_, v_x_406_, v_x_407_);
v___x_469_ = ((size_t)7ULL);
v___x_470_ = lean_usize_dec_le(v___x_469_, v_x_405_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_461_);
v___x_472_ = lean_unsigned_to_nat(4u);
v___x_473_ = lean_nat_dec_lt(v___x_471_, v___x_472_);
lean_dec(v___x_471_);
v___y_463_ = v___x_473_;
goto v___jp_462_;
}
else
{
v___y_463_ = v___x_470_;
goto v___jp_462_;
}
v___jp_462_:
{
if (v___y_463_ == 0)
{
lean_object* v_ks_464_; lean_object* v_vs_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v_ks_464_ = lean_ctor_get(v_newNode_461_, 0);
lean_inc_ref(v_ks_464_);
v_vs_465_ = lean_ctor_get(v_newNode_461_, 1);
lean_inc_ref(v_vs_465_);
lean_dec_ref(v_newNode_461_);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__2);
v___x_468_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_x_405_, v_ks_464_, v_vs_465_, v___x_466_, v___x_467_);
lean_dec_ref(v_vs_465_);
lean_dec_ref(v_ks_464_);
return v___x_468_;
}
else
{
return v_newNode_461_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(size_t v_depth_476_, lean_object* v_keys_477_, lean_object* v_vals_478_, lean_object* v_i_479_, lean_object* v_entries_480_){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_array_get_size(v_keys_477_);
v___x_482_ = lean_nat_dec_lt(v_i_479_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec(v_i_479_);
return v_entries_480_;
}
else
{
lean_object* v_k_483_; lean_object* v_v_484_; uint64_t v___x_485_; size_t v_h_486_; size_t v___x_487_; lean_object* v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v_h_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_k_483_ = lean_array_fget_borrowed(v_keys_477_, v_i_479_);
v_v_484_ = lean_array_fget_borrowed(v_vals_478_, v_i_479_);
v___x_485_ = l_Lean_instHashableMVarId_hash(v_k_483_);
v_h_486_ = lean_uint64_to_usize(v___x_485_);
v___x_487_ = ((size_t)5ULL);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_sub(v_depth_476_, v___x_489_);
v___x_491_ = lean_usize_mul(v___x_487_, v___x_490_);
v_h_492_ = lean_usize_shift_right(v_h_486_, v___x_491_);
v___x_493_ = lean_nat_add(v_i_479_, v___x_488_);
lean_dec(v_i_479_);
lean_inc(v_v_484_);
lean_inc(v_k_483_);
v___x_494_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_entries_480_, v_h_492_, v_depth_476_, v_k_483_, v_v_484_);
v_i_479_ = v___x_493_;
v_entries_480_ = v___x_494_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_depth_496_, lean_object* v_keys_497_, lean_object* v_vals_498_, lean_object* v_i_499_, lean_object* v_entries_500_){
_start:
{
size_t v_depth_boxed_501_; lean_object* v_res_502_; 
v_depth_boxed_501_ = lean_unbox_usize(v_depth_496_);
lean_dec(v_depth_496_);
v_res_502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_boxed_501_, v_keys_497_, v_vals_498_, v_i_499_, v_entries_500_);
lean_dec_ref(v_vals_498_);
lean_dec_ref(v_keys_497_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_503_, lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
size_t v_x_8767__boxed_508_; size_t v_x_8768__boxed_509_; lean_object* v_res_510_; 
v_x_8767__boxed_508_ = lean_unbox_usize(v_x_504_);
lean_dec(v_x_504_);
v_x_8768__boxed_509_ = lean_unbox_usize(v_x_505_);
lean_dec(v_x_505_);
v_res_510_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_503_, v_x_8767__boxed_508_, v_x_8768__boxed_509_, v_x_506_, v_x_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
uint64_t v___x_514_; size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_514_ = l_Lean_instHashableMVarId_hash(v_x_512_);
v___x_515_ = lean_uint64_to_usize(v___x_514_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_511_, v___x_515_, v___x_516_, v_x_512_, v_x_513_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object* v_mvarId_518_, lean_object* v_val_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; lean_object* v_mctx_523_; lean_object* v_cache_524_; lean_object* v_zetaDeltaFVarIds_525_; lean_object* v_postponed_526_; lean_object* v_diag_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_554_; 
v___x_522_ = lean_st_ref_take(v___y_520_);
v_mctx_523_ = lean_ctor_get(v___x_522_, 0);
v_cache_524_ = lean_ctor_get(v___x_522_, 1);
v_zetaDeltaFVarIds_525_ = lean_ctor_get(v___x_522_, 2);
v_postponed_526_ = lean_ctor_get(v___x_522_, 3);
v_diag_527_ = lean_ctor_get(v___x_522_, 4);
v_isSharedCheck_554_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_554_ == 0)
{
v___x_529_ = v___x_522_;
v_isShared_530_ = v_isSharedCheck_554_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_diag_527_);
lean_inc(v_postponed_526_);
lean_inc(v_zetaDeltaFVarIds_525_);
lean_inc(v_cache_524_);
lean_inc(v_mctx_523_);
lean_dec(v___x_522_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_554_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_depth_531_; lean_object* v_levelAssignDepth_532_; lean_object* v_mvarCounter_533_; lean_object* v_lDepth_534_; lean_object* v_decls_535_; lean_object* v_userNames_536_; lean_object* v_lAssignment_537_; lean_object* v_eAssignment_538_; lean_object* v_dAssignment_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_553_; 
v_depth_531_ = lean_ctor_get(v_mctx_523_, 0);
v_levelAssignDepth_532_ = lean_ctor_get(v_mctx_523_, 1);
v_mvarCounter_533_ = lean_ctor_get(v_mctx_523_, 2);
v_lDepth_534_ = lean_ctor_get(v_mctx_523_, 3);
v_decls_535_ = lean_ctor_get(v_mctx_523_, 4);
v_userNames_536_ = lean_ctor_get(v_mctx_523_, 5);
v_lAssignment_537_ = lean_ctor_get(v_mctx_523_, 6);
v_eAssignment_538_ = lean_ctor_get(v_mctx_523_, 7);
v_dAssignment_539_ = lean_ctor_get(v_mctx_523_, 8);
v_isSharedCheck_553_ = !lean_is_exclusive(v_mctx_523_);
if (v_isSharedCheck_553_ == 0)
{
v___x_541_ = v_mctx_523_;
v_isShared_542_ = v_isSharedCheck_553_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_dAssignment_539_);
lean_inc(v_eAssignment_538_);
lean_inc(v_lAssignment_537_);
lean_inc(v_userNames_536_);
lean_inc(v_decls_535_);
lean_inc(v_lDepth_534_);
lean_inc(v_mvarCounter_533_);
lean_inc(v_levelAssignDepth_532_);
lean_inc(v_depth_531_);
lean_dec(v_mctx_523_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_553_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_543_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_538_, v_mvarId_518_, v_val_519_);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 7, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_depth_531_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_levelAssignDepth_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 2, v_mvarCounter_533_);
lean_ctor_set(v_reuseFailAlloc_552_, 3, v_lDepth_534_);
lean_ctor_set(v_reuseFailAlloc_552_, 4, v_decls_535_);
lean_ctor_set(v_reuseFailAlloc_552_, 5, v_userNames_536_);
lean_ctor_set(v_reuseFailAlloc_552_, 6, v_lAssignment_537_);
lean_ctor_set(v_reuseFailAlloc_552_, 7, v___x_543_);
lean_ctor_set(v_reuseFailAlloc_552_, 8, v_dAssignment_539_);
v___x_545_ = v_reuseFailAlloc_552_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_547_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_545_);
v___x_547_ = v___x_529_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_551_, 1, v_cache_524_);
lean_ctor_set(v_reuseFailAlloc_551_, 2, v_zetaDeltaFVarIds_525_);
lean_ctor_set(v_reuseFailAlloc_551_, 3, v_postponed_526_);
lean_ctor_set(v_reuseFailAlloc_551_, 4, v_diag_527_);
v___x_547_ = v_reuseFailAlloc_551_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_st_ref_set(v___y_520_, v___x_547_);
v___x_549_ = lean_box(0);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
return v___x_550_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg___boxed(lean_object* v_mvarId_555_, lean_object* v_val_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_555_, v_val_556_, v___y_557_);
lean_dec(v___y_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(lean_object* v_msgData_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; lean_object* v_env_567_; lean_object* v___x_568_; lean_object* v_mctx_569_; lean_object* v_lctx_570_; lean_object* v_options_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_566_ = lean_st_ref_get(v___y_564_);
v_env_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_env_567_);
lean_dec(v___x_566_);
v___x_568_ = lean_st_ref_get(v___y_562_);
v_mctx_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc_ref(v_mctx_569_);
lean_dec(v___x_568_);
v_lctx_570_ = lean_ctor_get(v___y_561_, 2);
v_options_571_ = lean_ctor_get(v___y_563_, 2);
lean_inc_ref(v_options_571_);
lean_inc_ref(v_lctx_570_);
v___x_572_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_572_, 0, v_env_567_);
lean_ctor_set(v___x_572_, 1, v_mctx_569_);
lean_ctor_set(v___x_572_, 2, v_lctx_570_);
lean_ctor_set(v___x_572_, 3, v_options_571_);
v___x_573_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
lean_ctor_set(v___x_573_, 1, v_msgData_560_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_ref_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_598_; 
v_ref_588_ = lean_ctor_get(v___y_585_, 5);
v___x_589_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_598_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_598_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_596_; 
lean_inc(v_ref_588_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_ref_588_);
lean_ctor_set(v___x_594_, 1, v_a_590_);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 1);
lean_ctor_set(v___x_592_, 0, v___x_594_);
v___x_596_ = v___x_592_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___x_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_606_, lean_object* v_b_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_array_613_; lean_object* v_start_614_; lean_object* v_stop_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_630_; 
v_array_613_ = lean_ctor_get(v_a_606_, 0);
v_start_614_ = lean_ctor_get(v_a_606_, 1);
v_stop_615_ = lean_ctor_get(v_a_606_, 2);
v_isSharedCheck_630_ = !lean_is_exclusive(v_a_606_);
if (v_isSharedCheck_630_ == 0)
{
v___x_617_ = v_a_606_;
v_isShared_618_ = v_isSharedCheck_630_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_stop_615_);
lean_inc(v_start_614_);
lean_inc(v_array_613_);
lean_dec(v_a_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_630_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_lt(v_start_614_, v_stop_615_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_del_object(v___x_617_);
lean_dec(v_stop_615_);
lean_dec(v_start_614_);
lean_dec_ref(v_array_613_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_b_607_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_array_fget_borrowed(v_array_613_, v_start_614_);
lean_inc(v___x_621_);
v___x_622_ = l_Lean_Meta_mkCongrFun(v_b_607_, v___x_621_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref(v___x_622_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_start_614_, v___x_624_);
lean_dec(v_start_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_625_);
v___x_627_ = v___x_617_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_array_613_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_stop_615_);
v___x_627_ = v_reuseFailAlloc_629_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
v_a_606_ = v___x_627_;
v_b_607_ = v_a_623_;
goto _start;
}
}
else
{
lean_del_object(v___x_617_);
lean_dec(v_stop_615_);
lean_dec(v_start_614_);
lean_dec_ref(v_array_613_);
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_631_, v_b_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_639_, lean_object* v___x_640_, size_t v_sz_641_, size_t v_i_642_, lean_object* v_bs_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_lt(v_i_642_, v_sz_641_);
if (v___x_644_ == 0)
{
lean_dec(v_levels_639_);
return v_bs_643_;
}
else
{
lean_object* v_v_645_; lean_object* v_toConstantVal_646_; lean_object* v_name_647_; lean_object* v___x_648_; lean_object* v_bs_x27_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; size_t v___x_653_; size_t v___x_654_; lean_object* v___x_655_; 
v_v_645_ = lean_array_uget_borrowed(v_bs_643_, v_i_642_);
v_toConstantVal_646_ = lean_ctor_get(v_v_645_, 0);
v_name_647_ = lean_ctor_get(v_toConstantVal_646_, 0);
lean_inc(v_name_647_);
v___x_648_ = lean_unsigned_to_nat(0u);
v_bs_x27_649_ = lean_array_uset(v_bs_643_, v_i_642_, v___x_648_);
v___x_650_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_647_);
lean_inc(v_levels_639_);
v___x_651_ = l_Lean_mkConst(v___x_650_, v_levels_639_);
v___x_652_ = l_Lean_mkAppN(v___x_651_, v___x_640_);
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_add(v_i_642_, v___x_653_);
v___x_655_ = lean_array_uset(v_bs_x27_649_, v_i_642_, v___x_652_);
v_i_642_ = v___x_654_;
v_bs_643_ = v___x_655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_657_, lean_object* v___x_658_, lean_object* v_sz_659_, lean_object* v_i_660_, lean_object* v_bs_661_){
_start:
{
size_t v_sz_boxed_662_; size_t v_i_boxed_663_; lean_object* v_res_664_; 
v_sz_boxed_662_ = lean_unbox_usize(v_sz_659_);
lean_dec(v_sz_659_);
v_i_boxed_663_ = lean_unbox_usize(v_i_660_);
lean_dec(v_i_660_);
v_res_664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_657_, v___x_658_, v_sz_boxed_662_, v_i_boxed_663_, v_bs_661_);
lean_dec_ref(v___x_658_);
return v_res_664_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0));
v___x_667_ = l_Lean_stringToMessageData(v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object* v_infos_671_, lean_object* v_numParams_672_, lean_object* v___x_673_, lean_object* v_name_674_, lean_object* v_levels_675_, lean_object* v_args_676_, lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; size_t v_sz_694_; size_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_683_ = lean_array_get_size(v_infos_671_);
v___x_684_ = lean_nat_sub(v_numParams_672_, v___x_683_);
lean_inc(v___x_673_);
lean_inc_ref(v_args_676_);
v___x_685_ = l_Array_toSubarray___redArg(v_args_676_, v___x_673_, v___x_684_);
v___x_686_ = lean_array_get_size(v_args_676_);
v___x_687_ = l_Array_toSubarray___redArg(v_args_676_, v_numParams_672_, v___x_686_);
lean_inc_n(v_name_674_, 2);
v___x_688_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_674_);
lean_inc_n(v_levels_675_, 3);
lean_inc(v___x_688_);
v___x_689_ = l_Lean_mkConst(v___x_688_, v_levels_675_);
v___x_690_ = l_Subarray_copy___redArg(v___x_685_);
v___x_691_ = l_Lean_mkAppN(v___x_689_, v___x_690_);
lean_inc_ref(v___x_687_);
v___x_692_ = l_Subarray_copy___redArg(v___x_687_);
v___x_693_ = l_Lean_mkAppN(v___x_691_, v___x_692_);
v_sz_694_ = lean_array_size(v_infos_671_);
v___x_695_ = ((size_t)0ULL);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_675_, v___x_690_, v_sz_694_, v___x_695_, v_infos_671_);
v___x_697_ = l_Lean_mkConst(v_name_674_, v_levels_675_);
lean_inc_ref(v___x_690_);
v___x_698_ = l_Array_append___redArg(v___x_690_, v___x_696_);
lean_dec_ref(v___x_696_);
v___x_699_ = l_Array_append___redArg(v___x_698_, v___x_692_);
v___x_700_ = l_Lean_mkAppN(v___x_697_, v___x_699_);
lean_dec_ref(v___x_699_);
v___x_701_ = l_Lean_Meta_mkEq(v___x_693_, v___x_700_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_768_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_768_ == 0)
{
v___x_704_ = v___x_701_;
v_isShared_705_ = v_isSharedCheck_768_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_701_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_768_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set_tag(v___x_704_, 1);
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_767_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
uint8_t v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = 0;
v___x_709_ = lean_box(0);
v___x_710_ = l_Lean_Meta_mkFreshExprMVar(v___x_707_, v___x_708_, v___x_709_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref(v___x_710_);
v___x_712_ = l_Lean_Meta_getEqnsFor_x3f(v___x_688_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref(v___x_712_);
if (lean_obj_tag(v_a_713_) == 1)
{
lean_object* v_val_721_; lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v_val_721_ = lean_ctor_get(v_a_713_, 0);
lean_inc(v_val_721_);
lean_dec_ref(v_a_713_);
v___x_722_ = lean_array_get_size(v_val_721_);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_dec_eq(v___x_722_, v___x_723_);
if (v___x_724_ == 0)
{
lean_dec(v_val_721_);
lean_dec(v_a_711_);
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_687_);
lean_dec(v_levels_675_);
lean_dec(v_name_674_);
lean_dec(v___x_673_);
v___y_715_ = v___y_678_;
v___y_716_ = v___y_679_;
v___y_717_ = v___y_680_;
v___y_718_ = v___y_681_;
goto v___jp_714_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_725_ = lean_array_fget(v_val_721_, v___x_673_);
lean_dec(v___x_673_);
lean_dec(v_val_721_);
v___x_726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3));
v___x_727_ = l_Lean_Name_append(v_name_674_, v___x_726_);
lean_inc(v_levels_675_);
v___x_728_ = l_Lean_mkConst(v___x_727_, v_levels_675_);
v___x_729_ = l_Lean_mkConst(v___x_725_, v_levels_675_);
v___x_730_ = l_Lean_mkAppN(v___x_729_, v___x_690_);
v___x_731_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_687_, v___x_730_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; uint8_t v___x_734_; lean_object* v___x_735_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref(v___x_731_);
v___x_733_ = l_Lean_Expr_mvarId_x21(v_a_711_);
v___x_734_ = 0;
v___x_735_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_733_, v___x_728_, v___x_734_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref(v___x_735_);
v___x_737_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_736_, v_a_732_, v___y_679_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; 
lean_dec_ref(v___x_737_);
v___x_738_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_711_, v___y_679_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_object* v_a_739_; lean_object* v___x_740_; uint8_t v___x_741_; lean_object* v___x_742_; 
v_a_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_a_739_);
lean_dec_ref(v___x_738_);
v___x_740_ = l_Array_append___redArg(v___x_690_, v___x_692_);
lean_dec_ref(v___x_692_);
v___x_741_ = 1;
v___x_742_ = l_Lean_Meta_mkLambdaFVars(v___x_740_, v_a_739_, v___x_734_, v___x_724_, v___x_734_, v___x_724_, v___x_741_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec_ref(v___x_740_);
return v___x_742_;
}
else
{
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
return v___x_738_;
}
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v_a_711_);
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
v_a_743_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_737_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_737_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec(v_a_732_);
lean_dec(v_a_711_);
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
v_a_751_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_735_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_735_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
else
{
lean_dec_ref(v___x_728_);
lean_dec(v_a_711_);
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
return v___x_731_;
}
}
}
else
{
lean_dec(v_a_713_);
lean_dec(v_a_711_);
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_687_);
lean_dec(v_levels_675_);
lean_dec(v_name_674_);
lean_dec(v___x_673_);
v___y_715_ = v___y_678_;
v___y_716_ = v___y_679_;
v___y_717_ = v___y_680_;
v___y_718_ = v___y_681_;
goto v___jp_714_;
}
v___jp_714_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
v___x_720_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_719_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_720_;
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_dec(v_a_711_);
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
lean_dec_ref(v___x_687_);
lean_dec(v_levels_675_);
lean_dec(v_name_674_);
lean_dec(v___x_673_);
v_a_759_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_712_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_712_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
else
{
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
lean_dec(v___x_688_);
lean_dec_ref(v___x_687_);
lean_dec(v_levels_675_);
lean_dec(v_name_674_);
lean_dec(v___x_673_);
return v___x_710_;
}
}
}
}
else
{
lean_dec_ref(v___x_692_);
lean_dec_ref(v___x_690_);
lean_dec(v___x_688_);
lean_dec_ref(v___x_687_);
lean_dec(v_levels_675_);
lean_dec(v_name_674_);
lean_dec(v___x_673_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object* v_infos_769_, lean_object* v_numParams_770_, lean_object* v___x_771_, lean_object* v_name_772_, lean_object* v_levels_773_, lean_object* v_args_774_, lean_object* v_x_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_769_, v_numParams_770_, v___x_771_, v_name_772_, v_levels_773_, v_args_774_, v_x_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec_ref(v_x_775_);
return v_res_781_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0(void){
_start:
{
lean_object* v___x_782_; double v___x_783_; 
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_float_of_nat(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_787_, lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_ref_794_; lean_object* v___x_795_; lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_840_; 
v_ref_794_ = lean_ctor_get(v___y_791_, 5);
v___x_795_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_840_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_840_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_840_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v_traceState_801_; lean_object* v_env_802_; lean_object* v_nextMacroScope_803_; lean_object* v_ngen_804_; lean_object* v_auxDeclNGen_805_; lean_object* v_cache_806_; lean_object* v_messages_807_; lean_object* v_infoState_808_; lean_object* v_snapshotTasks_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_839_; 
v___x_800_ = lean_st_ref_take(v___y_792_);
v_traceState_801_ = lean_ctor_get(v___x_800_, 4);
v_env_802_ = lean_ctor_get(v___x_800_, 0);
v_nextMacroScope_803_ = lean_ctor_get(v___x_800_, 1);
v_ngen_804_ = lean_ctor_get(v___x_800_, 2);
v_auxDeclNGen_805_ = lean_ctor_get(v___x_800_, 3);
v_cache_806_ = lean_ctor_get(v___x_800_, 5);
v_messages_807_ = lean_ctor_get(v___x_800_, 6);
v_infoState_808_ = lean_ctor_get(v___x_800_, 7);
v_snapshotTasks_809_ = lean_ctor_get(v___x_800_, 8);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_839_ == 0)
{
v___x_811_ = v___x_800_;
v_isShared_812_ = v_isSharedCheck_839_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_snapshotTasks_809_);
lean_inc(v_infoState_808_);
lean_inc(v_messages_807_);
lean_inc(v_cache_806_);
lean_inc(v_traceState_801_);
lean_inc(v_auxDeclNGen_805_);
lean_inc(v_ngen_804_);
lean_inc(v_nextMacroScope_803_);
lean_inc(v_env_802_);
lean_dec(v___x_800_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_839_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint64_t v_tid_813_; lean_object* v_traces_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_838_; 
v_tid_813_ = lean_ctor_get_uint64(v_traceState_801_, sizeof(void*)*1);
v_traces_814_ = lean_ctor_get(v_traceState_801_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v_traceState_801_);
if (v_isSharedCheck_838_ == 0)
{
v___x_816_ = v_traceState_801_;
v_isShared_817_ = v_isSharedCheck_838_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_traces_814_);
lean_dec(v_traceState_801_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_838_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_818_; double v___x_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_818_ = lean_box(0);
v___x_819_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_820_ = 0;
v___x_821_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_822_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_822_, 0, v_cls_787_);
lean_ctor_set(v___x_822_, 1, v___x_818_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
lean_ctor_set_float(v___x_822_, sizeof(void*)*3, v___x_819_);
lean_ctor_set_float(v___x_822_, sizeof(void*)*3 + 8, v___x_819_);
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*3 + 16, v___x_820_);
v___x_823_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_824_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v_a_796_);
lean_ctor_set(v___x_824_, 2, v___x_823_);
lean_inc(v_ref_794_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_ref_794_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_PersistentArray_push___redArg(v_traces_814_, v___x_825_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_826_);
v___x_828_ = v___x_816_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_826_);
lean_ctor_set_uint64(v_reuseFailAlloc_837_, sizeof(void*)*1, v_tid_813_);
v___x_828_ = v_reuseFailAlloc_837_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_830_; 
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 4, v___x_828_);
v___x_830_ = v___x_811_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_env_802_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_nextMacroScope_803_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_ngen_804_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_auxDeclNGen_805_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v___x_828_);
lean_ctor_set(v_reuseFailAlloc_836_, 5, v_cache_806_);
lean_ctor_set(v_reuseFailAlloc_836_, 6, v_messages_807_);
lean_ctor_set(v_reuseFailAlloc_836_, 7, v_infoState_808_);
lean_ctor_set(v_reuseFailAlloc_836_, 8, v_snapshotTasks_809_);
v___x_830_ = v_reuseFailAlloc_836_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_831_ = lean_st_ref_set(v___y_792_, v___x_830_);
v___x_832_ = lean_box(0);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_832_);
v___x_834_ = v___x_798_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
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
lean_object* v_a_874_; lean_object* v_toConstantVal_875_; lean_object* v_numParams_876_; lean_object* v_name_877_; lean_object* v_levelParams_878_; lean_object* v_type_879_; lean_object* v___x_880_; lean_object* v___f_881_; uint8_t v___x_882_; lean_object* v___x_883_; 
v_a_874_ = lean_array_uget_borrowed(v_as_863_, v_i_865_);
v_toConstantVal_875_ = lean_ctor_get(v_a_874_, 0);
v_numParams_876_ = lean_ctor_get(v_a_874_, 1);
v_name_877_ = lean_ctor_get(v_toConstantVal_875_, 0);
v_levelParams_878_ = lean_ctor_get(v_toConstantVal_875_, 1);
v_type_879_ = lean_ctor_get(v_toConstantVal_875_, 2);
v___x_880_ = lean_unsigned_to_nat(0u);
lean_inc(v_levels_862_);
lean_inc(v_name_877_);
lean_inc(v_numParams_876_);
lean_inc_ref(v_infos_861_);
v___f_881_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed), 12, 5);
lean_closure_set(v___f_881_, 0, v_infos_861_);
lean_closure_set(v___f_881_, 1, v_numParams_876_);
lean_closure_set(v___f_881_, 2, v___x_880_);
lean_closure_set(v___f_881_, 3, v_name_877_);
lean_closure_set(v___f_881_, 4, v_levels_862_);
v___x_882_ = 0;
lean_inc_ref(v_type_879_);
v___x_883_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_879_, v___f_881_, v___x_882_, v___x_882_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_options_884_; lean_object* v_a_885_; lean_object* v_inheritedTraceOptions_886_; uint8_t v_hasTrace_887_; lean_object* v___x_888_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; lean_object* v___y_893_; 
v_options_884_ = lean_ctor_get(v___y_869_, 2);
v_a_885_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_883_);
v_inheritedTraceOptions_886_ = lean_ctor_get(v___y_869_, 13);
v_hasTrace_887_ = lean_ctor_get_uint8(v_options_884_, sizeof(void*)*1);
v___x_888_ = lean_box(0);
if (v_hasTrace_887_ == 0)
{
v___y_890_ = v___y_867_;
v___y_891_ = v___y_868_;
v___y_892_ = v___y_869_;
v___y_893_ = v___y_870_;
goto v___jp_889_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_924_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_925_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_886_, v_options_884_, v___x_924_);
if (v___x_925_ == 0)
{
v___y_890_ = v___y_867_;
v___y_891_ = v___y_868_;
v___y_892_ = v___y_869_;
v___y_893_ = v___y_870_;
goto v___jp_889_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_926_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
lean_inc(v_a_885_);
v___x_927_ = l_Lean_MessageData_ofExpr(v_a_885_);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_923_, v___x_928_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_dec_ref(v___x_929_);
v___y_890_ = v___y_867_;
v___y_891_ = v___y_868_;
v___y_892_ = v___y_869_;
v___y_893_ = v___y_870_;
goto v___jp_889_;
}
else
{
lean_dec(v_a_885_);
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
return v___x_929_;
}
}
}
v___jp_889_:
{
lean_object* v___x_894_; 
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v___y_890_);
lean_inc(v_a_885_);
v___x_894_ = lean_infer_type(v_a_885_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
lean_inc(v_name_877_);
v___x_896_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_877_);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_898_ = l_Lean_Name_append(v___x_896_, v___x_897_);
v___x_899_ = lean_box(0);
lean_inc(v_levelParams_878_);
v___x_900_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_898_, v_levelParams_878_, v_a_895_, v_a_885_, v___x_899_, v___y_893_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
v___x_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_902_, 0, v_a_901_);
v___x_903_ = l_Lean_addDecl(v___x_902_, v___x_882_, v___y_892_, v___y_893_);
if (lean_obj_tag(v___x_903_) == 0)
{
size_t v___x_904_; size_t v___x_905_; 
lean_dec_ref(v___x_903_);
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_add(v_i_865_, v___x_904_);
v_i_865_ = v___x_905_;
v_b_866_ = v___x_888_;
goto _start;
}
else
{
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
return v___x_903_;
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
v_a_907_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_900_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_900_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_a_885_);
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
v_a_915_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_894_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_894_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_levels_862_);
lean_dec_ref(v_infos_861_);
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
size_t v_x_9701__boxed_1056_; size_t v_x_9702__boxed_1057_; lean_object* v_res_1058_; 
v_x_9701__boxed_1056_ = lean_unbox_usize(v_x_1052_);
lean_dec(v_x_1052_);
v_x_9702__boxed_1057_ = lean_unbox_usize(v_x_1053_);
lean_dec(v_x_1053_);
v_res_1058_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_1050_, v_x_1051_, v_x_9701__boxed_1056_, v_x_9702__boxed_1057_, v_x_1054_, v_x_1055_);
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
v___x_1107_ = lean_st_ref_set(v___y_1088_, v___x_1106_);
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
lean_object* v___x_1222_; uint8_t v___y_1224_; uint8_t v___y_1231_; lean_object* v_env_1234_; uint8_t v___x_1235_; 
v___x_1222_ = lean_st_ref_get(v___y_1220_);
v_env_1234_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref_n(v_env_1234_, 2);
lean_dec(v___x_1222_);
v___x_1235_ = l_Lean_Environment_hasUnsafe(v_env_1234_, v_type_1217_);
if (v___x_1235_ == 0)
{
uint8_t v___x_1236_; 
v___x_1236_ = l_Lean_Environment_hasUnsafe(v_env_1234_, v_value_1218_);
v___y_1231_ = v___x_1236_;
goto v___jp_1230_;
}
else
{
lean_dec_ref(v_env_1234_);
v___y_1231_ = v___x_1235_;
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
if (v___y_1231_ == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = 1;
v___y_1224_ = v___x_1232_;
goto v___jp_1223_;
}
else
{
uint8_t v___x_1233_; 
v___x_1233_ = 0;
v___y_1224_ = v___x_1233_;
goto v___jp_1223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1237_, lean_object* v_levelParams_1238_, lean_object* v_type_1239_, lean_object* v_value_1240_, lean_object* v_hints_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1237_, v_levelParams_1238_, v_type_1239_, v_value_1240_, v_hints_1241_, v___y_1242_);
lean_dec(v___y_1242_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1245_, lean_object* v_levelParams_1246_, lean_object* v_type_1247_, lean_object* v_value_1248_, lean_object* v_hints_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1245_, v_levelParams_1246_, v_type_1247_, v_value_1248_, v_hints_1249_, v___y_1255_);
return v___x_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1258_, lean_object* v_levelParams_1259_, lean_object* v_type_1260_, lean_object* v_value_1261_, lean_object* v_hints_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1258_, v_levelParams_1259_, v_type_1260_, v_value_1261_, v_hints_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1271_, lean_object* v_maxFVars_x3f_1272_, lean_object* v_k_1273_, uint8_t v_cleanupAnnotations_1274_, uint8_t v_whnfType_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___f_1283_; lean_object* v___x_1284_; 
lean_inc(v___y_1277_);
lean_inc_ref(v___y_1276_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1283_, 0, v_k_1273_);
lean_closure_set(v___f_1283_, 1, v___y_1276_);
lean_closure_set(v___f_1283_, 2, v___y_1277_);
v___x_1284_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1271_, v_maxFVars_x3f_1272_, v___f_1283_, v_cleanupAnnotations_1274_, v_whnfType_1275_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1284_) == 0)
{
return v___x_1284_;
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1293_, lean_object* v_maxFVars_x3f_1294_, lean_object* v_k_1295_, lean_object* v_cleanupAnnotations_1296_, lean_object* v_whnfType_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1305_; uint8_t v_whnfType_boxed_1306_; lean_object* v_res_1307_; 
v_cleanupAnnotations_boxed_1305_ = lean_unbox(v_cleanupAnnotations_1296_);
v_whnfType_boxed_1306_ = lean_unbox(v_whnfType_1297_);
v_res_1307_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1293_, v_maxFVars_x3f_1294_, v_k_1295_, v_cleanupAnnotations_boxed_1305_, v_whnfType_boxed_1306_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v___y_1300_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1308_, lean_object* v_type_1309_, lean_object* v_maxFVars_x3f_1310_, lean_object* v_k_1311_, uint8_t v_cleanupAnnotations_1312_, uint8_t v_whnfType_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1309_, v_maxFVars_x3f_1310_, v_k_1311_, v_cleanupAnnotations_1312_, v_whnfType_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1322_, lean_object* v_type_1323_, lean_object* v_maxFVars_x3f_1324_, lean_object* v_k_1325_, lean_object* v_cleanupAnnotations_1326_, lean_object* v_whnfType_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1335_; uint8_t v_whnfType_boxed_1336_; lean_object* v_res_1337_; 
v_cleanupAnnotations_boxed_1335_ = lean_unbox(v_cleanupAnnotations_1326_);
v_whnfType_boxed_1336_ = lean_unbox(v_whnfType_1327_);
v_res_1337_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1322_, v_type_1323_, v_maxFVars_x3f_1324_, v_k_1325_, v_cleanupAnnotations_boxed_1335_, v_whnfType_boxed_1336_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_options_1346_; uint8_t v_hasTrace_1347_; 
v_options_1346_ = lean_ctor_get(v___y_1343_, 2);
v_hasTrace_1347_ = lean_ctor_get_uint8(v_options_1346_, sizeof(void*)*1);
if (v_hasTrace_1347_ == 0)
{
lean_object* v___x_1348_; lean_object* v___x_1349_; 
lean_dec(v_cls_1338_);
v___x_1348_ = lean_box(v_hasTrace_1347_);
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
return v___x_1349_;
}
else
{
lean_object* v_inheritedTraceOptions_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_inheritedTraceOptions_1350_ = lean_ctor_get(v___y_1343_, 13);
v___x_1351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1352_ = l_Lean_Name_append(v___x_1351_, v_cls_1338_);
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
lean_object* v___x_1369_; lean_object* v_mctx_1370_; lean_object* v_cache_1371_; lean_object* v_zetaDeltaFVarIds_1372_; lean_object* v_postponed_1373_; lean_object* v_diag_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1401_; 
v___x_1369_ = lean_st_ref_take(v___y_1367_);
v_mctx_1370_ = lean_ctor_get(v___x_1369_, 0);
v_cache_1371_ = lean_ctor_get(v___x_1369_, 1);
v_zetaDeltaFVarIds_1372_ = lean_ctor_get(v___x_1369_, 2);
v_postponed_1373_ = lean_ctor_get(v___x_1369_, 3);
v_diag_1374_ = lean_ctor_get(v___x_1369_, 4);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1376_ = v___x_1369_;
v_isShared_1377_ = v_isSharedCheck_1401_;
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
v_isShared_1377_ = v_isSharedCheck_1401_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_depth_1378_; lean_object* v_levelAssignDepth_1379_; lean_object* v_mvarCounter_1380_; lean_object* v_lDepth_1381_; lean_object* v_decls_1382_; lean_object* v_userNames_1383_; lean_object* v_lAssignment_1384_; lean_object* v_eAssignment_1385_; lean_object* v_dAssignment_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1400_; 
v_depth_1378_ = lean_ctor_get(v_mctx_1370_, 0);
v_levelAssignDepth_1379_ = lean_ctor_get(v_mctx_1370_, 1);
v_mvarCounter_1380_ = lean_ctor_get(v_mctx_1370_, 2);
v_lDepth_1381_ = lean_ctor_get(v_mctx_1370_, 3);
v_decls_1382_ = lean_ctor_get(v_mctx_1370_, 4);
v_userNames_1383_ = lean_ctor_get(v_mctx_1370_, 5);
v_lAssignment_1384_ = lean_ctor_get(v_mctx_1370_, 6);
v_eAssignment_1385_ = lean_ctor_get(v_mctx_1370_, 7);
v_dAssignment_1386_ = lean_ctor_get(v_mctx_1370_, 8);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_mctx_1370_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1388_ = v_mctx_1370_;
v_isShared_1389_ = v_isSharedCheck_1400_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_dAssignment_1386_);
lean_inc(v_eAssignment_1385_);
lean_inc(v_lAssignment_1384_);
lean_inc(v_userNames_1383_);
lean_inc(v_decls_1382_);
lean_inc(v_lDepth_1381_);
lean_inc(v_mvarCounter_1380_);
lean_inc(v_levelAssignDepth_1379_);
lean_inc(v_depth_1378_);
lean_dec(v_mctx_1370_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1400_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1390_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1385_, v_mvarId_1365_, v_val_1366_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 7, v___x_1390_);
v___x_1392_ = v___x_1388_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_depth_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_levelAssignDepth_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_mvarCounter_1380_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_lDepth_1381_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_decls_1382_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v_userNames_1383_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v_lAssignment_1384_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_dAssignment_1386_);
v___x_1392_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1394_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 0, v___x_1392_);
v___x_1394_ = v___x_1376_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_cache_1371_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_zetaDeltaFVarIds_1372_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_postponed_1373_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_diag_1374_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_st_ref_set(v___y_1367_, v___x_1394_);
v___x_1396_ = lean_box(0);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
return v___x_1397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_mvarId_1402_, lean_object* v_val_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1402_, v_val_1403_, v___y_1404_);
lean_dec(v___y_1404_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_cls_1407_, lean_object* v_msg_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_ref_1414_; lean_object* v___x_1415_; lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1460_; 
v_ref_1414_ = lean_ctor_get(v___y_1411_, 5);
v___x_1415_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1460_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1460_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v_traceState_1421_; lean_object* v_env_1422_; lean_object* v_nextMacroScope_1423_; lean_object* v_ngen_1424_; lean_object* v_auxDeclNGen_1425_; lean_object* v_cache_1426_; lean_object* v_messages_1427_; lean_object* v_infoState_1428_; lean_object* v_snapshotTasks_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1459_; 
v___x_1420_ = lean_st_ref_take(v___y_1412_);
v_traceState_1421_ = lean_ctor_get(v___x_1420_, 4);
v_env_1422_ = lean_ctor_get(v___x_1420_, 0);
v_nextMacroScope_1423_ = lean_ctor_get(v___x_1420_, 1);
v_ngen_1424_ = lean_ctor_get(v___x_1420_, 2);
v_auxDeclNGen_1425_ = lean_ctor_get(v___x_1420_, 3);
v_cache_1426_ = lean_ctor_get(v___x_1420_, 5);
v_messages_1427_ = lean_ctor_get(v___x_1420_, 6);
v_infoState_1428_ = lean_ctor_get(v___x_1420_, 7);
v_snapshotTasks_1429_ = lean_ctor_get(v___x_1420_, 8);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1431_ = v___x_1420_;
v_isShared_1432_ = v_isSharedCheck_1459_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snapshotTasks_1429_);
lean_inc(v_infoState_1428_);
lean_inc(v_messages_1427_);
lean_inc(v_cache_1426_);
lean_inc(v_traceState_1421_);
lean_inc(v_auxDeclNGen_1425_);
lean_inc(v_ngen_1424_);
lean_inc(v_nextMacroScope_1423_);
lean_inc(v_env_1422_);
lean_dec(v___x_1420_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1459_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
uint64_t v_tid_1433_; lean_object* v_traces_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1458_; 
v_tid_1433_ = lean_ctor_get_uint64(v_traceState_1421_, sizeof(void*)*1);
v_traces_1434_ = lean_ctor_get(v_traceState_1421_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_traceState_1421_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1436_ = v_traceState_1421_;
v_isShared_1437_ = v_isSharedCheck_1458_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_traces_1434_);
lean_dec(v_traceState_1421_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1458_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; double v___x_1439_; uint8_t v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_1440_ = 0;
v___x_1441_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_1442_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1442_, 0, v_cls_1407_);
lean_ctor_set(v___x_1442_, 1, v___x_1438_);
lean_ctor_set(v___x_1442_, 2, v___x_1441_);
lean_ctor_set_float(v___x_1442_, sizeof(void*)*3, v___x_1439_);
lean_ctor_set_float(v___x_1442_, sizeof(void*)*3 + 8, v___x_1439_);
lean_ctor_set_uint8(v___x_1442_, sizeof(void*)*3 + 16, v___x_1440_);
v___x_1443_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_1444_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v_a_1416_);
lean_ctor_set(v___x_1444_, 2, v___x_1443_);
lean_inc(v_ref_1414_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_ref_1414_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = l_Lean_PersistentArray_push___redArg(v_traces_1434_, v___x_1445_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v___x_1446_);
v___x_1448_ = v___x_1436_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1446_);
lean_ctor_set_uint64(v_reuseFailAlloc_1457_, sizeof(void*)*1, v_tid_1433_);
v___x_1448_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1450_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 4, v___x_1448_);
v___x_1450_ = v___x_1431_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_env_1422_);
lean_ctor_set(v_reuseFailAlloc_1456_, 1, v_nextMacroScope_1423_);
lean_ctor_set(v_reuseFailAlloc_1456_, 2, v_ngen_1424_);
lean_ctor_set(v_reuseFailAlloc_1456_, 3, v_auxDeclNGen_1425_);
lean_ctor_set(v_reuseFailAlloc_1456_, 4, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1456_, 5, v_cache_1426_);
lean_ctor_set(v_reuseFailAlloc_1456_, 6, v_messages_1427_);
lean_ctor_set(v_reuseFailAlloc_1456_, 7, v_infoState_1428_);
lean_ctor_set(v_reuseFailAlloc_1456_, 8, v_snapshotTasks_1429_);
v___x_1450_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1454_; 
v___x_1451_ = lean_st_ref_set(v___y_1412_, v___x_1450_);
v___x_1452_ = lean_box(0);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 0, v___x_1452_);
v___x_1454_ = v___x_1418_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_cls_1461_, lean_object* v_msg_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1461_, v_msg_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
return v_res_1468_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1469_; lean_object* v_dummy_1470_; 
v___x_1469_ = lean_box(0);
v_dummy_1470_ = l_Lean_Expr_sort___override(v___x_1469_);
return v_dummy_1470_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1));
v___x_1473_ = l_Lean_stringToMessageData(v___x_1472_);
return v___x_1473_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3));
v___x_1476_ = l_Lean_stringToMessageData(v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v_numParams_1477_, lean_object* v___x_1478_, lean_object* v_name_1479_, lean_object* v___x_1480_, lean_object* v___x_1481_, lean_object* v_name_1482_, lean_object* v___x_1483_, lean_object* v_cls_1484_, lean_object* v_fields_1485_, lean_object* v_bodyExpr_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_options_1494_; lean_object* v_inheritedTraceOptions_1495_; uint8_t v_hasTrace_1496_; lean_object* v_nargs_1497_; lean_object* v_dummy_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; 
v_options_1494_ = lean_ctor_get(v___y_1491_, 2);
v_inheritedTraceOptions_1495_ = lean_ctor_get(v___y_1491_, 13);
v_hasTrace_1496_ = lean_ctor_get_uint8(v_options_1494_, sizeof(void*)*1);
v_nargs_1497_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1486_);
v_dummy_1498_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
lean_inc(v_nargs_1497_);
v___x_1499_ = lean_mk_array(v_nargs_1497_, v_dummy_1498_);
v___x_1500_ = lean_unsigned_to_nat(1u);
v___x_1501_ = lean_nat_sub(v_nargs_1497_, v___x_1500_);
lean_dec(v_nargs_1497_);
v___x_1502_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1486_, v___x_1499_, v___x_1501_);
v___x_1503_ = lean_array_get_size(v___x_1502_);
v___x_1504_ = lean_nat_add(v_numParams_1477_, v___x_1478_);
v___x_1505_ = l_Array_toSubarray___redArg(v___x_1502_, v___x_1504_, v___x_1503_);
v___x_1506_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1479_);
lean_inc(v___x_1480_);
lean_inc(v___x_1506_);
v___x_1507_ = l_Lean_mkConst(v___x_1506_, v___x_1480_);
v___x_1508_ = l_Lean_mkAppN(v___x_1507_, v___x_1481_);
v___x_1509_ = l_Subarray_copy___redArg(v___x_1505_);
v___x_1510_ = l_Lean_mkAppN(v___x_1508_, v___x_1509_);
lean_dec_ref(v___x_1509_);
if (v_hasTrace_1496_ == 0)
{
lean_dec(v_cls_1484_);
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
v___y_1514_ = v___y_1489_;
v___y_1515_ = v___y_1490_;
v___y_1516_ = v___y_1491_;
v___y_1517_ = v___y_1492_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v___x_1566_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
lean_inc(v_cls_1484_);
v___x_1567_ = l_Lean_Name_append(v___x_1566_, v_cls_1484_);
v___x_1568_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1495_, v_options_1494_, v___x_1567_);
lean_dec(v___x_1567_);
if (v___x_1568_ == 0)
{
lean_dec(v_cls_1484_);
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
v___y_1514_ = v___y_1489_;
v___y_1515_ = v___y_1490_;
v___y_1516_ = v___y_1491_;
v___y_1517_ = v___y_1492_;
goto v___jp_1511_;
}
else
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1569_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
lean_inc(v_name_1482_);
v___x_1570_ = l_Lean_MessageData_ofName(v_name_1482_);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
lean_inc_ref(v___x_1510_);
v___x_1574_ = l_Lean_MessageData_ofExpr(v___x_1510_);
v___x_1575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set(v___x_1575_, 1, v___x_1574_);
v___x_1576_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1484_, v___x_1575_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_dec_ref(v___x_1576_);
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
v___y_1514_ = v___y_1489_;
v___y_1515_ = v___y_1490_;
v___y_1516_ = v___y_1491_;
v___y_1517_ = v___y_1492_;
goto v___jp_1511_;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___x_1510_);
lean_dec(v___x_1506_);
lean_dec(v_name_1482_);
lean_dec(v___x_1480_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
v___jp_1511_:
{
lean_object* v___x_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1510_);
v___x_1519_ = 0;
v___x_1520_ = lean_box(0);
v___x_1521_ = l_Lean_Meta_mkFreshExprMVar(v___x_1518_, v___x_1519_, v___x_1520_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_Expr_mvarId_x21(v_a_1522_);
lean_inc(v___x_1523_);
v___x_1524_ = l_Lean_MVarId_getType(v___x_1523_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1527_ = l_Lean_Name_append(v___x_1506_, v___x_1526_);
lean_inc(v___x_1480_);
v___x_1528_ = l_Lean_mkConst(v___x_1527_, v___x_1480_);
v___x_1529_ = l_Lean_mkAppN(v___x_1528_, v___x_1481_);
v___x_1530_ = 0;
v___x_1531_ = 1;
v___x_1532_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1523_);
v___x_1533_ = l_Lean_MVarId_rewrite(v___x_1523_, v_a_1525_, v___x_1529_, v___x_1530_, v___x_1532_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v_eNew_1535_; lean_object* v_eqProof_1536_; lean_object* v___x_1537_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v___x_1533_);
v_eNew_1535_ = lean_ctor_get(v_a_1534_, 0);
lean_inc_ref(v_eNew_1535_);
v_eqProof_1536_ = lean_ctor_get(v_a_1534_, 1);
lean_inc_ref(v_eqProof_1536_);
lean_dec(v_a_1534_);
v___x_1537_ = l_Lean_MVarId_replaceTargetEq(v___x_1523_, v_eNew_1535_, v_eqProof_1536_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v_a_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref(v___x_1537_);
v___x_1539_ = l_Lean_mkConst(v_name_1482_, v___x_1480_);
v___x_1540_ = l_Lean_mkAppN(v___x_1539_, v___x_1481_);
v___x_1541_ = l_Lean_mkAppN(v___x_1540_, v___x_1483_);
v___x_1542_ = l_Lean_mkAppN(v___x_1541_, v_fields_1485_);
v___x_1543_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_1538_, v___x_1542_, v___y_1515_);
lean_dec_ref(v___x_1543_);
v___x_1544_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1522_, v___y_1515_);
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = 1;
v___x_1547_ = l_Lean_Meta_mkLambdaFVars(v_fields_1485_, v_a_1545_, v___x_1530_, v___x_1531_, v___x_1530_, v___x_1531_, v___x_1546_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
v___x_1549_ = l_Lean_Meta_mkLambdaFVars(v___x_1481_, v_a_1548_, v___x_1530_, v___x_1531_, v___x_1530_, v___x_1531_, v___x_1546_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1549_;
}
else
{
return v___x_1547_;
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_a_1522_);
lean_dec(v_name_1482_);
lean_dec(v___x_1480_);
v_a_1550_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1537_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1537_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
else
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec(v___x_1523_);
lean_dec(v_a_1522_);
lean_dec(v_name_1482_);
lean_dec(v___x_1480_);
v_a_1558_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1533_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1533_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
else
{
lean_dec(v___x_1523_);
lean_dec(v_a_1522_);
lean_dec(v___x_1506_);
lean_dec(v_name_1482_);
lean_dec(v___x_1480_);
return v___x_1524_;
}
}
else
{
lean_dec(v___x_1506_);
lean_dec(v_name_1482_);
lean_dec(v___x_1480_);
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_1585_ = _args[0];
lean_object* v___x_1586_ = _args[1];
lean_object* v_name_1587_ = _args[2];
lean_object* v___x_1588_ = _args[3];
lean_object* v___x_1589_ = _args[4];
lean_object* v_name_1590_ = _args[5];
lean_object* v___x_1591_ = _args[6];
lean_object* v_cls_1592_ = _args[7];
lean_object* v_fields_1593_ = _args[8];
lean_object* v_bodyExpr_1594_ = _args[9];
lean_object* v___y_1595_ = _args[10];
lean_object* v___y_1596_ = _args[11];
lean_object* v___y_1597_ = _args[12];
lean_object* v___y_1598_ = _args[13];
lean_object* v___y_1599_ = _args[14];
lean_object* v___y_1600_ = _args[15];
lean_object* v___y_1601_ = _args[16];
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1585_, v___x_1586_, v_name_1587_, v___x_1588_, v___x_1589_, v_name_1590_, v___x_1591_, v_cls_1592_, v_fields_1593_, v_bodyExpr_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_fields_1593_);
lean_dec_ref(v___x_1591_);
lean_dec_ref(v___x_1589_);
lean_dec(v___x_1586_);
lean_dec(v_numParams_1585_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1603_, size_t v_sz_1604_, size_t v_i_1605_, lean_object* v_bs_1606_){
_start:
{
uint8_t v___x_1607_; 
v___x_1607_ = lean_usize_dec_lt(v_i_1605_, v_sz_1604_);
if (v___x_1607_ == 0)
{
return v_bs_1606_;
}
else
{
lean_object* v_v_1608_; lean_object* v___x_1609_; lean_object* v_bs_x27_1610_; lean_object* v___x_1611_; size_t v___x_1612_; size_t v___x_1613_; lean_object* v___x_1614_; 
v_v_1608_ = lean_array_uget(v_bs_1606_, v_i_1605_);
v___x_1609_ = lean_unsigned_to_nat(0u);
v_bs_x27_1610_ = lean_array_uset(v_bs_1606_, v_i_1605_, v___x_1609_);
v___x_1611_ = l_Lean_mkAppN(v_v_1608_, v___x_1603_);
v___x_1612_ = ((size_t)1ULL);
v___x_1613_ = lean_usize_add(v_i_1605_, v___x_1612_);
v___x_1614_ = lean_array_uset(v_bs_x27_1610_, v_i_1605_, v___x_1611_);
v_i_1605_ = v___x_1613_;
v_bs_1606_ = v___x_1614_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1616_, lean_object* v_sz_1617_, lean_object* v_i_1618_, lean_object* v_bs_1619_){
_start:
{
size_t v_sz_boxed_1620_; size_t v_i_boxed_1621_; lean_object* v_res_1622_; 
v_sz_boxed_1620_ = lean_unbox_usize(v_sz_1617_);
lean_dec(v_sz_1617_);
v_i_boxed_1621_ = lean_unbox_usize(v_i_1618_);
lean_dec(v_i_1618_);
v_res_1622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1616_, v_sz_boxed_1620_, v_i_boxed_1621_, v_bs_1619_);
lean_dec_ref(v___x_1616_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1623_, size_t v_sz_1624_, size_t v_i_1625_, lean_object* v_bs_1626_){
_start:
{
uint8_t v___x_1627_; 
v___x_1627_ = lean_usize_dec_lt(v_i_1625_, v_sz_1624_);
if (v___x_1627_ == 0)
{
lean_dec(v___x_1623_);
return v_bs_1626_;
}
else
{
lean_object* v_v_1628_; lean_object* v___x_1629_; lean_object* v_bs_x27_1630_; lean_object* v___x_1631_; size_t v___x_1632_; size_t v___x_1633_; lean_object* v___x_1634_; 
v_v_1628_ = lean_array_uget(v_bs_1626_, v_i_1625_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v_bs_x27_1630_ = lean_array_uset(v_bs_1626_, v_i_1625_, v___x_1629_);
lean_inc(v___x_1623_);
v___x_1631_ = l_Lean_mkConst(v_v_1628_, v___x_1623_);
v___x_1632_ = ((size_t)1ULL);
v___x_1633_ = lean_usize_add(v_i_1625_, v___x_1632_);
v___x_1634_ = lean_array_uset(v_bs_x27_1630_, v_i_1625_, v___x_1631_);
v_i_1625_ = v___x_1633_;
v_bs_1626_ = v___x_1634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1636_, lean_object* v_sz_1637_, lean_object* v_i_1638_, lean_object* v_bs_1639_){
_start:
{
size_t v_sz_boxed_1640_; size_t v_i_boxed_1641_; lean_object* v_res_1642_; 
v_sz_boxed_1640_ = lean_unbox_usize(v_sz_1637_);
lean_dec(v_sz_1637_);
v_i_boxed_1641_ = lean_unbox_usize(v_i_1638_);
lean_dec(v_i_1638_);
v_res_1642_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1636_, v_sz_boxed_1640_, v_i_boxed_1641_, v_bs_1639_);
return v_res_1642_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object* v___x_1646_, lean_object* v_numParams_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, size_t v___x_1650_, lean_object* v___x_1651_, lean_object* v_name_1652_, lean_object* v_name_1653_, lean_object* v_cls_1654_, lean_object* v___f_1655_, lean_object* v_levelParams_1656_, lean_object* v_ctorSyntax_1657_, lean_object* v_args_1658_, lean_object* v_body_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; size_t v_sz_1670_; lean_object* v___x_1671_; size_t v_sz_1672_; lean_object* v___x_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; uint8_t v___x_1677_; lean_object* v___x_1678_; 
lean_inc_n(v_numParams_1647_, 2);
v___x_1667_ = l_Array_extract___redArg(v_args_1658_, v___x_1646_, v_numParams_1647_);
v___x_1668_ = lean_array_get_size(v_args_1658_);
v___x_1669_ = l_Array_toSubarray___redArg(v_args_1658_, v_numParams_1647_, v___x_1668_);
v_sz_1670_ = lean_array_size(v___x_1648_);
lean_inc(v___x_1649_);
v___x_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1649_, v_sz_1670_, v___x_1650_, v___x_1648_);
v_sz_1672_ = lean_array_size(v___x_1671_);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1667_, v_sz_1672_, v___x_1650_, v___x_1671_);
lean_inc(v_cls_1654_);
lean_inc_ref(v___x_1673_);
lean_inc(v_name_1653_);
v___f_1674_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1674_, 0, v_numParams_1647_);
lean_closure_set(v___f_1674_, 1, v___x_1651_);
lean_closure_set(v___f_1674_, 2, v_name_1652_);
lean_closure_set(v___f_1674_, 3, v___x_1649_);
lean_closure_set(v___f_1674_, 4, v___x_1667_);
lean_closure_set(v___f_1674_, 5, v_name_1653_);
lean_closure_set(v___f_1674_, 6, v___x_1673_);
lean_closure_set(v___f_1674_, 7, v_cls_1654_);
v___x_1675_ = l_Subarray_copy___redArg(v___x_1669_);
v___x_1676_ = l_Lean_Expr_replaceFVars(v_body_1659_, v___x_1675_, v___x_1673_);
lean_dec_ref(v___x_1673_);
lean_dec_ref(v___x_1675_);
v___x_1677_ = 0;
v___x_1678_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_1676_, v___f_1674_, v___x_1677_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1680_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_n(v_a_1679_, 2);
lean_dec_ref(v___x_1678_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
v___x_1680_ = lean_infer_type(v_a_1679_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v___y_1688_; lean_object* v___x_1705_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
lean_inc(v___y_1665_);
lean_inc_ref(v___y_1664_);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
v___x_1705_ = lean_apply_7(v___f_1655_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, lean_box(0));
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; uint8_t v___x_1707_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
if (v___x_1707_ == 0)
{
lean_dec(v_cls_1654_);
v___y_1683_ = v___y_1660_;
v___y_1684_ = v___y_1661_;
v___y_1685_ = v___y_1662_;
v___y_1686_ = v___y_1663_;
v___y_1687_ = v___y_1664_;
v___y_1688_ = v___y_1665_;
goto v___jp_1682_;
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1708_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
lean_inc(v_a_1681_);
v___x_1709_ = l_Lean_MessageData_ofExpr(v_a_1681_);
v___x_1710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1708_);
lean_ctor_set(v___x_1710_, 1, v___x_1709_);
v___x_1711_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1654_, v___x_1710_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_dec_ref(v___x_1711_);
v___y_1683_ = v___y_1660_;
v___y_1684_ = v___y_1661_;
v___y_1685_ = v___y_1662_;
v___y_1686_ = v___y_1663_;
v___y_1687_ = v___y_1664_;
v___y_1688_ = v___y_1665_;
goto v___jp_1682_;
}
else
{
lean_dec(v_a_1681_);
lean_dec(v_a_1679_);
lean_dec(v_ctorSyntax_1657_);
lean_dec(v_levelParams_1656_);
lean_dec(v_name_1653_);
return v___x_1711_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_a_1681_);
lean_dec(v_a_1679_);
lean_dec(v_ctorSyntax_1657_);
lean_dec(v_levelParams_1656_);
lean_dec(v_cls_1654_);
lean_dec(v_name_1653_);
v_a_1712_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1705_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1705_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
v___jp_1682_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1704_; 
v___x_1689_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1653_);
v___x_1690_ = lean_box(0);
lean_inc(v_a_1679_);
v___x_1691_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1689_, v_levelParams_1656_, v_a_1681_, v_a_1679_, v___x_1690_, v___y_1688_);
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1704_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1704_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1697_; 
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 1);
v___x_1697_ = v___x_1694_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1692_);
v___x_1697_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_addDecl(v___x_1697_, v___x_1677_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1698_) == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; lean_object* v___x_1702_; 
lean_dec_ref(v___x_1698_);
v___x_1699_ = lean_box(0);
v___x_1700_ = lean_box(0);
v___x_1701_ = 1;
v___x_1702_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1657_, v_a_1679_, v___x_1699_, v___x_1699_, v___x_1700_, v___x_1701_, v___x_1677_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1702_;
}
else
{
lean_dec(v_a_1679_);
lean_dec(v_ctorSyntax_1657_);
return v___x_1698_;
}
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec(v_a_1679_);
lean_dec(v_ctorSyntax_1657_);
lean_dec(v_levelParams_1656_);
lean_dec_ref(v___f_1655_);
lean_dec(v_cls_1654_);
lean_dec(v_name_1653_);
v_a_1720_ = lean_ctor_get(v___x_1680_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1680_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1680_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1680_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_dec(v_ctorSyntax_1657_);
lean_dec(v_levelParams_1656_);
lean_dec_ref(v___f_1655_);
lean_dec(v_cls_1654_);
lean_dec(v_name_1653_);
v_a_1728_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1678_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1678_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object** _args){
lean_object* v___x_1736_ = _args[0];
lean_object* v_numParams_1737_ = _args[1];
lean_object* v___x_1738_ = _args[2];
lean_object* v___x_1739_ = _args[3];
lean_object* v___x_1740_ = _args[4];
lean_object* v___x_1741_ = _args[5];
lean_object* v_name_1742_ = _args[6];
lean_object* v_name_1743_ = _args[7];
lean_object* v_cls_1744_ = _args[8];
lean_object* v___f_1745_ = _args[9];
lean_object* v_levelParams_1746_ = _args[10];
lean_object* v_ctorSyntax_1747_ = _args[11];
lean_object* v_args_1748_ = _args[12];
lean_object* v_body_1749_ = _args[13];
lean_object* v___y_1750_ = _args[14];
lean_object* v___y_1751_ = _args[15];
lean_object* v___y_1752_ = _args[16];
lean_object* v___y_1753_ = _args[17];
lean_object* v___y_1754_ = _args[18];
lean_object* v___y_1755_ = _args[19];
lean_object* v___y_1756_ = _args[20];
_start:
{
size_t v___x_9118__boxed_1757_; lean_object* v_res_1758_; 
v___x_9118__boxed_1757_ = lean_unbox_usize(v___x_1740_);
lean_dec(v___x_1740_);
v_res_1758_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1736_, v_numParams_1737_, v___x_1738_, v___x_1739_, v___x_9118__boxed_1757_, v___x_1741_, v_name_1742_, v_name_1743_, v_cls_1744_, v___f_1745_, v_levelParams_1746_, v_ctorSyntax_1747_, v_args_1748_, v_body_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec_ref(v_body_1749_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1759_, size_t v_i_1760_, lean_object* v_bs_1761_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_usize_dec_lt(v_i_1760_, v_sz_1759_);
if (v___x_1762_ == 0)
{
return v_bs_1761_;
}
else
{
lean_object* v_v_1763_; lean_object* v_toConstantVal_1764_; lean_object* v_name_1765_; lean_object* v___x_1766_; lean_object* v_bs_x27_1767_; lean_object* v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v_v_1763_ = lean_array_uget_borrowed(v_bs_1761_, v_i_1760_);
v_toConstantVal_1764_ = lean_ctor_get(v_v_1763_, 0);
v_name_1765_ = lean_ctor_get(v_toConstantVal_1764_, 0);
lean_inc(v_name_1765_);
v___x_1766_ = lean_unsigned_to_nat(0u);
v_bs_x27_1767_ = lean_array_uset(v_bs_1761_, v_i_1760_, v___x_1766_);
v___x_1768_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1765_);
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_add(v_i_1760_, v___x_1769_);
v___x_1771_ = lean_array_uset(v_bs_x27_1767_, v_i_1760_, v___x_1768_);
v_i_1760_ = v___x_1770_;
v_bs_1761_ = v___x_1771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1773_, lean_object* v_i_1774_, lean_object* v_bs_1775_){
_start:
{
size_t v_sz_boxed_1776_; size_t v_i_boxed_1777_; lean_object* v_res_1778_; 
v_sz_boxed_1776_ = lean_unbox_usize(v_sz_1773_);
lean_dec(v_sz_1773_);
v_i_boxed_1777_ = lean_unbox_usize(v_i_1774_);
lean_dec(v_i_1774_);
v_res_1778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1776_, v_i_boxed_1777_, v_bs_1775_);
return v_res_1778_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2(void){
_start:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1));
v___x_1783_ = l_Lean_stringToMessageData(v___x_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1786_, lean_object* v_ctorSyntax_1787_, lean_object* v_numParams_1788_, lean_object* v_name_1789_, lean_object* v_ctor_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v_cls_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1843_; 
v_cls_1798_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___f_1799_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1800_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1798_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1843_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1843_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; uint8_t v___x_1835_; 
v___x_1805_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1835_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1835_ == 0)
{
v___y_1807_ = v_a_1791_;
v___y_1808_ = v_a_1792_;
v___y_1809_ = v_a_1793_;
v___y_1810_ = v_a_1794_;
v___y_1811_ = v_a_1795_;
v___y_1812_ = v_a_1796_;
goto v___jp_1806_;
}
else
{
lean_object* v_toConstantVal_1836_; lean_object* v_name_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v_toConstantVal_1836_ = lean_ctor_get(v_ctor_1790_, 0);
v_name_1837_ = lean_ctor_get(v_toConstantVal_1836_, 0);
v___x_1838_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
lean_inc(v_name_1837_);
v___x_1839_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1837_);
v___x_1840_ = l_Lean_MessageData_ofName(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1838_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1798_, v___x_1841_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_dec_ref(v___x_1842_);
v___y_1807_ = v_a_1791_;
v___y_1808_ = v_a_1792_;
v___y_1809_ = v_a_1793_;
v___y_1810_ = v_a_1794_;
v___y_1811_ = v_a_1795_;
v___y_1812_ = v_a_1796_;
goto v___jp_1806_;
}
else
{
lean_del_object(v___x_1803_);
lean_dec_ref(v_ctor_1790_);
lean_dec(v_name_1789_);
lean_dec(v_numParams_1788_);
lean_dec(v_ctorSyntax_1787_);
lean_dec_ref(v_infos_1786_);
return v___x_1842_;
}
}
v___jp_1806_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_toConstantVal_1815_; lean_object* v_toConstantVal_1816_; lean_object* v_levelParams_1817_; lean_object* v_name_1818_; lean_object* v_levelParams_1819_; lean_object* v_type_1820_; lean_object* v___x_1821_; size_t v_sz_1822_; size_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___f_1828_; lean_object* v___x_1829_; lean_object* v___x_1831_; 
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = lean_array_get_borrowed(v___x_1805_, v_infos_1786_, v___x_1813_);
v_toConstantVal_1815_ = lean_ctor_get(v___x_1814_, 0);
v_toConstantVal_1816_ = lean_ctor_get(v_ctor_1790_, 0);
lean_inc_ref(v_toConstantVal_1816_);
lean_dec_ref(v_ctor_1790_);
v_levelParams_1817_ = lean_ctor_get(v_toConstantVal_1815_, 1);
lean_inc(v_levelParams_1817_);
v_name_1818_ = lean_ctor_get(v_toConstantVal_1816_, 0);
lean_inc(v_name_1818_);
v_levelParams_1819_ = lean_ctor_get(v_toConstantVal_1816_, 1);
lean_inc(v_levelParams_1819_);
v_type_1820_ = lean_ctor_get(v_toConstantVal_1816_, 2);
lean_inc_ref(v_type_1820_);
lean_dec_ref(v_toConstantVal_1816_);
v___x_1821_ = lean_array_get_size(v_infos_1786_);
v_sz_1822_ = lean_array_size(v_infos_1786_);
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1822_, v___x_1823_, v_infos_1786_);
v___x_1825_ = lean_box(0);
v___x_1826_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1817_, v___x_1825_);
v___x_1827_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1788_);
v___f_1828_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed), 21, 12);
lean_closure_set(v___f_1828_, 0, v___x_1813_);
lean_closure_set(v___f_1828_, 1, v_numParams_1788_);
lean_closure_set(v___f_1828_, 2, v___x_1824_);
lean_closure_set(v___f_1828_, 3, v___x_1826_);
lean_closure_set(v___f_1828_, 4, v___x_1827_);
lean_closure_set(v___f_1828_, 5, v___x_1821_);
lean_closure_set(v___f_1828_, 6, v_name_1789_);
lean_closure_set(v___f_1828_, 7, v_name_1818_);
lean_closure_set(v___f_1828_, 8, v_cls_1798_);
lean_closure_set(v___f_1828_, 9, v___f_1799_);
lean_closure_set(v___f_1828_, 10, v_levelParams_1819_);
lean_closure_set(v___f_1828_, 11, v_ctorSyntax_1787_);
v___x_1829_ = lean_nat_add(v_numParams_1788_, v___x_1821_);
lean_dec(v_numParams_1788_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 0, v___x_1829_);
v___x_1831_ = v___x_1803_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
uint8_t v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = 0;
v___x_1833_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1820_, v___x_1831_, v___f_1828_, v___x_1832_, v___x_1832_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
return v___x_1833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1844_, lean_object* v_ctorSyntax_1845_, lean_object* v_numParams_1846_, lean_object* v_name_1847_, lean_object* v_ctor_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1844_, v_ctorSyntax_1845_, v_numParams_1846_, v_name_1847_, v_ctor_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_mvarId_1857_, lean_object* v_val_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1857_, v_val_1858_, v___y_1862_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_mvarId_1867_, lean_object* v_val_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1867_, v_val_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
lean_dec(v___y_1874_);
lean_dec_ref(v___y_1873_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_cls_1877_, lean_object* v_msg_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1877_, v_msg_1878_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_cls_1887_, lean_object* v_msg_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1887_, v_msg_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
lean_dec(v___y_1894_);
lean_dec_ref(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1896_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l_instMonadEIO(lean_box(0));
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v_toApplicative_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_2005_; 
v___x_1912_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1913_ = l_StateRefT_x27_instMonad___redArg(v___x_1912_);
v_toApplicative_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1913_, 1);
lean_dec(v_unused_2006_);
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_2005_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_toApplicative_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_2005_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_toFunctor_1918_; lean_object* v_toSeq_1919_; lean_object* v_toSeqLeft_1920_; lean_object* v_toSeqRight_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_2003_; 
v_toFunctor_1918_ = lean_ctor_get(v_toApplicative_1914_, 0);
v_toSeq_1919_ = lean_ctor_get(v_toApplicative_1914_, 2);
v_toSeqLeft_1920_ = lean_ctor_get(v_toApplicative_1914_, 3);
v_toSeqRight_1921_ = lean_ctor_get(v_toApplicative_1914_, 4);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_toApplicative_1914_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_toApplicative_1914_, 1);
lean_dec(v_unused_2004_);
v___x_1923_ = v_toApplicative_1914_;
v_isShared_1924_ = v_isSharedCheck_2003_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_toSeqRight_1921_);
lean_inc(v_toSeqLeft_1920_);
lean_inc(v_toSeq_1919_);
lean_inc(v_toFunctor_1918_);
lean_dec(v_toApplicative_1914_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_2003_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___f_1925_; lean_object* v___f_1926_; lean_object* v___f_1927_; lean_object* v___f_1928_; lean_object* v___x_1929_; lean_object* v___f_1930_; lean_object* v___f_1931_; lean_object* v___f_1932_; lean_object* v___x_1934_; 
v___f_1925_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1926_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1918_);
v___f_1927_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1927_, 0, v_toFunctor_1918_);
v___f_1928_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1928_, 0, v_toFunctor_1918_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___f_1927_);
lean_ctor_set(v___x_1929_, 1, v___f_1928_);
v___f_1930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1930_, 0, v_toSeqRight_1921_);
v___f_1931_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1931_, 0, v_toSeqLeft_1920_);
v___f_1932_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1932_, 0, v_toSeq_1919_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 4, v___f_1930_);
lean_ctor_set(v___x_1923_, 3, v___f_1931_);
lean_ctor_set(v___x_1923_, 2, v___f_1932_);
lean_ctor_set(v___x_1923_, 1, v___f_1925_);
lean_ctor_set(v___x_1923_, 0, v___x_1929_);
v___x_1934_ = v___x_1923_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___f_1925_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v___f_1932_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v___f_1931_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v___f_1930_);
v___x_1934_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v___f_1926_);
lean_ctor_set(v___x_1916_, 0, v___x_1934_);
v___x_1936_ = v___x_1916_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1934_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___f_1926_);
v___x_1936_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
lean_object* v___x_1937_; lean_object* v_toApplicative_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1999_; 
v___x_1937_ = l_StateRefT_x27_instMonad___redArg(v___x_1936_);
v_toApplicative_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1999_ == 0)
{
lean_object* v_unused_2000_; 
v_unused_2000_ = lean_ctor_get(v___x_1937_, 1);
lean_dec(v_unused_2000_);
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1999_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_toApplicative_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1999_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_toFunctor_1942_; lean_object* v_toSeq_1943_; lean_object* v_toSeqLeft_1944_; lean_object* v_toSeqRight_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1997_; 
v_toFunctor_1942_ = lean_ctor_get(v_toApplicative_1938_, 0);
v_toSeq_1943_ = lean_ctor_get(v_toApplicative_1938_, 2);
v_toSeqLeft_1944_ = lean_ctor_get(v_toApplicative_1938_, 3);
v_toSeqRight_1945_ = lean_ctor_get(v_toApplicative_1938_, 4);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_toApplicative_1938_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v_toApplicative_1938_, 1);
lean_dec(v_unused_1998_);
v___x_1947_ = v_toApplicative_1938_;
v_isShared_1948_ = v_isSharedCheck_1997_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_toSeqRight_1945_);
lean_inc(v_toSeqLeft_1944_);
lean_inc(v_toSeq_1943_);
lean_inc(v_toFunctor_1942_);
lean_dec(v_toApplicative_1938_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1997_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___x_1953_; lean_object* v___f_1954_; lean_object* v___f_1955_; lean_object* v___f_1956_; lean_object* v___x_1958_; 
v___f_1949_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1950_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1942_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toFunctor_1942_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toFunctor_1942_);
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___f_1951_);
lean_ctor_set(v___x_1953_, 1, v___f_1952_);
v___f_1954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1954_, 0, v_toSeqRight_1945_);
v___f_1955_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1955_, 0, v_toSeqLeft_1944_);
v___f_1956_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1956_, 0, v_toSeq_1943_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 4, v___f_1954_);
lean_ctor_set(v___x_1947_, 3, v___f_1955_);
lean_ctor_set(v___x_1947_, 2, v___f_1956_);
lean_ctor_set(v___x_1947_, 1, v___f_1949_);
lean_ctor_set(v___x_1947_, 0, v___x_1953_);
v___x_1958_ = v___x_1947_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___f_1949_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v___f_1956_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v___f_1955_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v___f_1954_);
v___x_1958_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1960_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v___f_1950_);
lean_ctor_set(v___x_1940_, 0, v___x_1958_);
v___x_1960_ = v___x_1940_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v___f_1950_);
v___x_1960_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1961_; lean_object* v_toApplicative_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1993_; 
v___x_1961_ = l_StateRefT_x27_instMonad___redArg(v___x_1960_);
v_toApplicative_1962_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1993_ == 0)
{
lean_object* v_unused_1994_; 
v_unused_1994_ = lean_ctor_get(v___x_1961_, 1);
lean_dec(v_unused_1994_);
v___x_1964_ = v___x_1961_;
v_isShared_1965_ = v_isSharedCheck_1993_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_toApplicative_1962_);
lean_dec(v___x_1961_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1993_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v_toFunctor_1966_; lean_object* v_toSeq_1967_; lean_object* v_toSeqLeft_1968_; lean_object* v_toSeqRight_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1991_; 
v_toFunctor_1966_ = lean_ctor_get(v_toApplicative_1962_, 0);
v_toSeq_1967_ = lean_ctor_get(v_toApplicative_1962_, 2);
v_toSeqLeft_1968_ = lean_ctor_get(v_toApplicative_1962_, 3);
v_toSeqRight_1969_ = lean_ctor_get(v_toApplicative_1962_, 4);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_toApplicative_1962_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v_toApplicative_1962_, 1);
lean_dec(v_unused_1992_);
v___x_1971_ = v_toApplicative_1962_;
v_isShared_1972_ = v_isSharedCheck_1991_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_toSeqRight_1969_);
lean_inc(v_toSeqLeft_1968_);
lean_inc(v_toSeq_1967_);
lean_inc(v_toFunctor_1966_);
lean_dec(v_toApplicative_1962_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1991_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___f_1975_; lean_object* v___f_1976_; lean_object* v___x_1977_; lean_object* v___f_1978_; lean_object* v___f_1979_; lean_object* v___f_1980_; lean_object* v___x_1982_; 
v___f_1973_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_1974_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1966_);
v___f_1975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1975_, 0, v_toFunctor_1966_);
v___f_1976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1976_, 0, v_toFunctor_1966_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___f_1975_);
lean_ctor_set(v___x_1977_, 1, v___f_1976_);
v___f_1978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1978_, 0, v_toSeqRight_1969_);
v___f_1979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1979_, 0, v_toSeqLeft_1968_);
v___f_1980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1980_, 0, v_toSeq_1967_);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 4, v___f_1978_);
lean_ctor_set(v___x_1971_, 3, v___f_1979_);
lean_ctor_set(v___x_1971_, 2, v___f_1980_);
lean_ctor_set(v___x_1971_, 1, v___f_1973_);
lean_ctor_set(v___x_1971_, 0, v___x_1977_);
v___x_1982_ = v___x_1971_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___f_1973_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v___f_1980_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v___f_1979_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v___f_1978_);
v___x_1982_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 1, v___f_1974_);
lean_ctor_set(v___x_1964_, 0, v___x_1982_);
v___x_1984_ = v___x_1964_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___f_1974_);
v___x_1984_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_3780__overap_1987_; lean_object* v___x_1988_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = l_instInhabitedOfMonad___redArg(v___x_1984_, v___x_1985_);
v___x_3780__overap_1987_ = lean_panic_fn_borrowed(v___x_1986_, v_msg_1904_);
lean_dec(v___x_1986_);
lean_inc(v___y_1910_);
lean_inc_ref(v___y_1909_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
v___x_1988_ = lean_apply_7(v___x_3780__overap_1987_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, lean_box(0));
return v___x_1988_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2015_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2016_, lean_object* v_opt_2017_){
_start:
{
lean_object* v_name_2018_; lean_object* v_defValue_2019_; lean_object* v_map_2020_; lean_object* v___x_2021_; 
v_name_2018_ = lean_ctor_get(v_opt_2017_, 0);
v_defValue_2019_ = lean_ctor_get(v_opt_2017_, 1);
v_map_2020_ = lean_ctor_get(v_opts_2016_, 0);
v___x_2021_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2020_, v_name_2018_);
if (lean_obj_tag(v___x_2021_) == 0)
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_unbox(v_defValue_2019_);
return v___x_2022_;
}
else
{
lean_object* v_val_2023_; 
v_val_2023_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_val_2023_);
lean_dec_ref(v___x_2021_);
if (lean_obj_tag(v_val_2023_) == 1)
{
uint8_t v_v_2024_; 
v_v_2024_ = lean_ctor_get_uint8(v_val_2023_, 0);
lean_dec_ref(v_val_2023_);
return v_v_2024_;
}
else
{
uint8_t v___x_2025_; 
lean_dec(v_val_2023_);
v___x_2025_ = lean_unbox(v_defValue_2019_);
return v___x_2025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2026_, lean_object* v_opt_2027_){
_start:
{
uint8_t v_res_2028_; lean_object* v_r_2029_; 
v_res_2028_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2026_, v_opt_2027_);
lean_dec_ref(v_opt_2027_);
lean_dec_ref(v_opts_2026_);
v_r_2029_ = lean_box(v_res_2028_);
return v_r_2029_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = lean_box(1);
v___x_2031_ = l_Lean_MessageData_ofFormat(v___x_2030_);
return v___x_2031_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2036_ = l_Lean_MessageData_ofFormat(v___x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2037_, lean_object* v_x_2038_){
_start:
{
if (lean_obj_tag(v_x_2038_) == 0)
{
return v_x_2037_;
}
else
{
lean_object* v_head_2039_; lean_object* v_tail_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2062_; 
v_head_2039_ = lean_ctor_get(v_x_2038_, 0);
v_tail_2040_ = lean_ctor_get(v_x_2038_, 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_x_2038_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2042_ = v_x_2038_;
v_isShared_2043_ = v_isSharedCheck_2062_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_tail_2040_);
lean_inc(v_head_2039_);
lean_dec(v_x_2038_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2062_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v_before_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2060_; 
v_before_2044_ = lean_ctor_get(v_head_2039_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_head_2039_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v_head_2039_, 1);
lean_dec(v_unused_2061_);
v___x_2046_ = v_head_2039_;
v_isShared_2047_ = v_isSharedCheck_2060_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_before_2044_);
lean_dec(v_head_2039_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2060_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2048_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 7);
lean_ctor_set(v___x_2046_, 1, v___x_2048_);
lean_ctor_set(v___x_2046_, 0, v_x_2037_);
v___x_2050_ = v___x_2046_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_x_2037_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2043_ == 0)
{
lean_ctor_set_tag(v___x_2042_, 7);
lean_ctor_set(v___x_2042_, 1, v___x_2051_);
lean_ctor_set(v___x_2042_, 0, v___x_2050_);
v___x_2053_ = v___x_2042_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = l_Lean_MessageData_ofSyntax(v_before_2044_);
v___x_2055_ = l_Lean_indentD(v___x_2054_);
v___x_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
lean_ctor_set(v___x_2056_, 1, v___x_2055_);
v_x_2037_ = v___x_2056_;
v_x_2038_ = v_tail_2040_;
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
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2067_ = l_Lean_MessageData_ofFormat(v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2068_, lean_object* v_macroStack_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_options_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v_options_2072_ = lean_ctor_get(v___y_2070_, 2);
v___x_2073_ = l_Lean_Elab_pp_macroStack;
v___x_2074_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_options_2072_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; 
lean_dec(v_macroStack_2069_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_msgData_2068_);
return v___x_2075_;
}
else
{
if (lean_obj_tag(v_macroStack_2069_) == 0)
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v_msgData_2068_);
return v___x_2076_;
}
else
{
lean_object* v_head_2077_; lean_object* v_after_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2093_; 
v_head_2077_ = lean_ctor_get(v_macroStack_2069_, 0);
lean_inc(v_head_2077_);
v_after_2078_ = lean_ctor_get(v_head_2077_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_head_2077_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v_head_2077_, 0);
lean_dec(v_unused_2094_);
v___x_2080_ = v_head_2077_;
v_isShared_2081_ = v_isSharedCheck_2093_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_after_2078_);
lean_dec(v_head_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2093_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2082_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 7);
lean_ctor_set(v___x_2080_, 1, v___x_2082_);
lean_ctor_set(v___x_2080_, 0, v_msgData_2068_);
v___x_2084_ = v___x_2080_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_msgData_2068_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2082_);
v___x_2084_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_msgData_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2085_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2084_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = l_Lean_MessageData_ofSyntax(v_after_2078_);
v___x_2088_ = l_Lean_indentD(v___x_2087_);
v_msgData_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2089_, 0, v___x_2086_);
lean_ctor_set(v_msgData_2089_, 1, v___x_2088_);
v___x_2090_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2089_, v_macroStack_2069_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
return v___x_2091_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2095_, lean_object* v_macroStack_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2095_, v_macroStack_2096_, v___y_2097_);
lean_dec_ref(v___y_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_ref_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v_macroStack_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2122_; 
v_ref_2108_ = lean_ctor_get(v___y_2105_, 5);
v___x_2109_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2100_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
v_macroStack_2111_ = lean_ctor_get(v___y_2101_, 1);
lean_inc_n(v_macroStack_2111_, 2);
v___x_2112_ = l_Lean_Elab_getBetterRef(v_ref_2108_, v_macroStack_2111_);
v___x_2113_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2110_, v_macroStack_2111_, v___y_2105_);
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2122_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2112_);
lean_ctor_set(v___x_2118_, 1, v_a_2114_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set_tag(v___x_2116_, 1);
lean_ctor_set(v___x_2116_, 0, v___x_2118_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
return v_res_2131_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2137_ = l_Lean_stringToMessageData(v___x_2136_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2141_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2142_ = lean_unsigned_to_nat(11u);
v___x_2143_ = lean_unsigned_to_nat(122u);
v___x_2144_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2145_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2146_ = l_mkPanicMessageWithDecl(v___x_2145_, v___x_2144_, v___x_2143_, v___x_2142_, v___x_2141_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2163_; lean_object* v_env_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; 
v___x_2163_ = lean_st_ref_get(v___y_2153_);
v_env_2164_ = lean_ctor_get(v___x_2163_, 0);
lean_inc_ref(v_env_2164_);
lean_dec(v___x_2163_);
v___x_2165_ = 0;
lean_inc(v_constName_2147_);
v___x_2166_ = l_Lean_Environment_findAsync_x3f(v_env_2164_, v_constName_2147_, v___x_2165_);
if (lean_obj_tag(v___x_2166_) == 1)
{
lean_object* v_val_2167_; uint8_t v_kind_2168_; 
v_val_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_val_2167_);
lean_dec_ref(v___x_2166_);
v_kind_2168_ = lean_ctor_get_uint8(v_val_2167_, sizeof(void*)*3);
if (v_kind_2168_ == 6)
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2167_);
if (lean_obj_tag(v___x_2169_) == 6)
{
lean_object* v_val_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec(v_constName_2147_);
v_val_2170_ = lean_ctor_get(v___x_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_val_2170_);
lean_dec(v___x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 0);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_val_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_dec_ref(v___x_2169_);
v___x_2178_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2179_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2178_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
if (lean_obj_tag(v_a_2180_) == 0)
{
lean_del_object(v___x_2182_);
goto v___jp_2155_;
}
else
{
lean_object* v_val_2184_; lean_object* v___x_2186_; 
lean_dec(v_constName_2147_);
v_val_2184_ = lean_ctor_get(v_a_2180_, 0);
lean_inc(v_val_2184_);
lean_dec_ref(v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v_val_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_val_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_constName_2147_);
v_a_2189_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2179_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2179_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
else
{
lean_dec(v_val_2167_);
goto v___jp_2155_;
}
}
else
{
lean_dec(v___x_2166_);
goto v___jp_2155_;
}
v___jp_2155_:
{
lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2156_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2157_ = 0;
v___x_2158_ = l_Lean_MessageData_ofConstName(v_constName_2147_, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2156_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2161_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
return v___x_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2206_, lean_object* v_infos_2207_, lean_object* v_numParams_2208_, lean_object* v_as_x27_2209_, lean_object* v_b_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
if (lean_obj_tag(v_as_x27_2209_) == 0)
{
lean_object* v___x_2218_; 
lean_dec(v_numParams_2208_);
lean_dec_ref(v_infos_2207_);
lean_dec_ref(v_a_2206_);
v___x_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2218_, 0, v_b_2210_);
return v___x_2218_;
}
else
{
lean_object* v_head_2219_; lean_object* v_tail_2220_; lean_object* v_array_2221_; lean_object* v_start_2222_; lean_object* v_stop_2223_; uint8_t v___x_2224_; 
v_head_2219_ = lean_ctor_get(v_as_x27_2209_, 0);
lean_inc(v_head_2219_);
v_tail_2220_ = lean_ctor_get(v_as_x27_2209_, 1);
lean_inc(v_tail_2220_);
lean_dec_ref(v_as_x27_2209_);
v_array_2221_ = lean_ctor_get(v_b_2210_, 0);
v_start_2222_ = lean_ctor_get(v_b_2210_, 1);
v_stop_2223_ = lean_ctor_get(v_b_2210_, 2);
v___x_2224_ = lean_nat_dec_lt(v_start_2222_, v_stop_2223_);
if (v___x_2224_ == 0)
{
lean_object* v___x_2225_; 
lean_dec(v_tail_2220_);
lean_dec(v_head_2219_);
lean_dec(v_numParams_2208_);
lean_dec_ref(v_infos_2207_);
lean_dec_ref(v_a_2206_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v_b_2210_);
return v___x_2225_;
}
else
{
lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2257_; 
lean_inc(v_stop_2223_);
lean_inc(v_start_2222_);
lean_inc_ref(v_array_2221_);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_b_2210_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; lean_object* v_unused_2259_; lean_object* v_unused_2260_; 
v_unused_2258_ = lean_ctor_get(v_b_2210_, 2);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_b_2210_, 1);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_b_2210_, 0);
lean_dec(v_unused_2260_);
v___x_2227_ = v_b_2210_;
v_isShared_2228_ = v_isSharedCheck_2257_;
goto v_resetjp_2226_;
}
else
{
lean_dec(v_b_2210_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2257_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; 
v___x_2229_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2219_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_toConstantVal_2230_; lean_object* v_a_2231_; lean_object* v_name_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_toConstantVal_2230_ = lean_ctor_get(v_a_2206_, 0);
v_a_2231_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2231_);
lean_dec_ref(v___x_2229_);
v_name_2232_ = lean_ctor_get(v_toConstantVal_2230_, 0);
v___x_2233_ = lean_array_fget_borrowed(v_array_2221_, v_start_2222_);
lean_inc(v_name_2232_);
lean_inc(v_numParams_2208_);
lean_inc(v___x_2233_);
lean_inc_ref(v_infos_2207_);
v___x_2234_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2207_, v___x_2233_, v_numParams_2208_, v_name_2232_, v_a_2231_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2238_; 
lean_dec_ref(v___x_2234_);
v___x_2235_ = lean_unsigned_to_nat(1u);
v___x_2236_ = lean_nat_add(v_start_2222_, v___x_2235_);
lean_dec(v_start_2222_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v___x_2236_);
v___x_2238_ = v___x_2227_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_array_2221_);
lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2236_);
lean_ctor_set(v_reuseFailAlloc_2240_, 2, v_stop_2223_);
v___x_2238_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
v_as_x27_2209_ = v_tail_2220_;
v_b_2210_ = v___x_2238_;
goto _start;
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
lean_del_object(v___x_2227_);
lean_dec(v_stop_2223_);
lean_dec(v_start_2222_);
lean_dec_ref(v_array_2221_);
lean_dec(v_tail_2220_);
lean_dec(v_numParams_2208_);
lean_dec_ref(v_infos_2207_);
lean_dec_ref(v_a_2206_);
v_a_2241_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2234_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2234_);
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
lean_del_object(v___x_2227_);
lean_dec(v_stop_2223_);
lean_dec(v_start_2222_);
lean_dec_ref(v_array_2221_);
lean_dec(v_tail_2220_);
lean_dec(v_numParams_2208_);
lean_dec_ref(v_infos_2207_);
lean_dec_ref(v_a_2206_);
v_a_2249_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2229_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2229_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2261_, lean_object* v_infos_2262_, lean_object* v_numParams_2263_, lean_object* v_as_x27_2264_, lean_object* v_b_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2261_, v_infos_2262_, v_numParams_2263_, v_as_x27_2264_, v_b_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2274_, lean_object* v_numParams_2275_, lean_object* v_as_2276_, size_t v_sz_2277_, size_t v_i_2278_, lean_object* v_b_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v___x_2287_; 
v___x_2287_ = lean_usize_dec_lt(v_i_2278_, v_sz_2277_);
if (v___x_2287_ == 0)
{
lean_object* v___x_2288_; 
lean_dec(v_numParams_2275_);
lean_dec_ref(v_infos_2274_);
v___x_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_b_2279_);
return v___x_2288_;
}
else
{
lean_object* v_array_2289_; lean_object* v_start_2290_; lean_object* v_stop_2291_; uint8_t v___x_2292_; 
v_array_2289_ = lean_ctor_get(v_b_2279_, 0);
v_start_2290_ = lean_ctor_get(v_b_2279_, 1);
v_stop_2291_ = lean_ctor_get(v_b_2279_, 2);
v___x_2292_ = lean_nat_dec_lt(v_start_2290_, v_stop_2291_);
if (v___x_2292_ == 0)
{
lean_object* v___x_2293_; 
lean_dec(v_numParams_2275_);
lean_dec_ref(v_infos_2274_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v_b_2279_);
return v___x_2293_;
}
else
{
lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2321_; 
lean_inc(v_stop_2291_);
lean_inc(v_start_2290_);
lean_inc_ref(v_array_2289_);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_b_2279_);
if (v_isSharedCheck_2321_ == 0)
{
lean_object* v_unused_2322_; lean_object* v_unused_2323_; lean_object* v_unused_2324_; 
v_unused_2322_ = lean_ctor_get(v_b_2279_, 2);
lean_dec(v_unused_2322_);
v_unused_2323_ = lean_ctor_get(v_b_2279_, 1);
lean_dec(v_unused_2323_);
v_unused_2324_ = lean_ctor_get(v_b_2279_, 0);
lean_dec(v_unused_2324_);
v___x_2295_ = v_b_2279_;
v_isShared_2296_ = v_isSharedCheck_2321_;
goto v_resetjp_2294_;
}
else
{
lean_dec(v_b_2279_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2321_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v_ctorSyntax_2298_; lean_object* v_a_2299_; lean_object* v_ctors_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2297_ = lean_array_fget_borrowed(v_array_2289_, v_start_2290_);
v_ctorSyntax_2298_ = lean_ctor_get(v___x_2297_, 4);
v_a_2299_ = lean_array_uget_borrowed(v_as_2276_, v_i_2278_);
v_ctors_2300_ = lean_ctor_get(v_a_2299_, 4);
v___x_2301_ = lean_array_get_size(v_ctorSyntax_2298_);
v___x_2302_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ctorSyntax_2298_);
v___x_2303_ = l_Array_toSubarray___redArg(v_ctorSyntax_2298_, v___x_2302_, v___x_2301_);
lean_inc(v_ctors_2300_);
lean_inc(v_numParams_2275_);
lean_inc_ref(v_infos_2274_);
lean_inc(v_a_2299_);
v___x_2304_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2299_, v_infos_2274_, v_numParams_2275_, v_ctors_2300_, v___x_2303_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
lean_dec_ref(v___x_2304_);
v___x_2305_ = lean_unsigned_to_nat(1u);
v___x_2306_ = lean_nat_add(v_start_2290_, v___x_2305_);
lean_dec(v_start_2290_);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 1, v___x_2306_);
v___x_2308_ = v___x_2295_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_array_2289_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_stop_2291_);
v___x_2308_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
size_t v___x_2309_; size_t v___x_2310_; 
v___x_2309_ = ((size_t)1ULL);
v___x_2310_ = lean_usize_add(v_i_2278_, v___x_2309_);
v_i_2278_ = v___x_2310_;
v_b_2279_ = v___x_2308_;
goto _start;
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_del_object(v___x_2295_);
lean_dec(v_stop_2291_);
lean_dec(v_start_2290_);
lean_dec_ref(v_array_2289_);
lean_dec(v_numParams_2275_);
lean_dec_ref(v_infos_2274_);
v_a_2313_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2304_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2304_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2325_, lean_object* v_numParams_2326_, lean_object* v_as_2327_, lean_object* v_sz_2328_, lean_object* v_i_2329_, lean_object* v_b_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
size_t v_sz_boxed_2338_; size_t v_i_boxed_2339_; lean_object* v_res_2340_; 
v_sz_boxed_2338_ = lean_unbox_usize(v_sz_2328_);
lean_dec(v_sz_2328_);
v_i_boxed_2339_ = lean_unbox_usize(v_i_2329_);
lean_dec(v_i_2329_);
v_res_2340_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2325_, v_numParams_2326_, v_as_2327_, v_sz_boxed_2338_, v_i_boxed_2339_, v_b_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec_ref(v_as_2327_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2341_, lean_object* v_infos_2342_, lean_object* v_coinductiveElabData_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; size_t v_sz_2354_; size_t v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = lean_unsigned_to_nat(0u);
v___x_2352_ = lean_array_get_size(v_coinductiveElabData_2343_);
v___x_2353_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2343_, v___x_2351_, v___x_2352_);
v_sz_2354_ = lean_array_size(v_infos_2342_);
v___x_2355_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2342_);
v___x_2356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2342_, v_numParams_2341_, v_infos_2342_, v_sz_2354_, v___x_2355_, v___x_2353_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_);
lean_dec_ref(v_infos_2342_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2364_; 
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2364_ == 0)
{
lean_object* v_unused_2365_; 
v_unused_2365_ = lean_ctor_get(v___x_2356_, 0);
lean_dec(v_unused_2365_);
v___x_2358_ = v___x_2356_;
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
else
{
lean_dec(v___x_2356_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = lean_box(0);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
v_a_2366_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2356_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2356_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2374_, lean_object* v_infos_2375_, lean_object* v_coinductiveElabData_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2374_, v_infos_2375_, v_coinductiveElabData_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2385_, lean_object* v_infos_2386_, lean_object* v_numParams_2387_, lean_object* v_as_2388_, lean_object* v_as_x27_2389_, lean_object* v_b_2390_, lean_object* v_a_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2385_, v_infos_2386_, v_numParams_2387_, v_as_x27_2389_, v_b_2390_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2400_, lean_object* v_infos_2401_, lean_object* v_numParams_2402_, lean_object* v_as_2403_, lean_object* v_as_x27_2404_, lean_object* v_b_2405_, lean_object* v_a_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2400_, v_infos_2401_, v_numParams_2402_, v_as_2403_, v_as_x27_2404_, v_b_2405_, v_a_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_as_2403_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2415_, lean_object* v_msg_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2425_, lean_object* v_msg_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2425_, v_msg_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2435_, lean_object* v_macroStack_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2435_, v_macroStack_2436_, v___y_2441_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2445_, lean_object* v_macroStack_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2445_, v_macroStack_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_type_2455_, lean_object* v_maxFVars_x3f_2456_, lean_object* v_k_2457_, uint8_t v_cleanupAnnotations_2458_, uint8_t v_whnfType_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___f_2465_; lean_object* v___x_2466_; 
v___f_2465_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2465_, 0, v_k_2457_);
v___x_2466_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2455_, v_maxFVars_x3f_2456_, v___f_2465_, v_cleanupAnnotations_2458_, v_whnfType_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2466_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2466_);
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
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
v_a_2475_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2466_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2466_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_type_2483_, lean_object* v_maxFVars_x3f_2484_, lean_object* v_k_2485_, lean_object* v_cleanupAnnotations_2486_, lean_object* v_whnfType_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2493_; uint8_t v_whnfType_boxed_2494_; lean_object* v_res_2495_; 
v_cleanupAnnotations_boxed_2493_ = lean_unbox(v_cleanupAnnotations_2486_);
v_whnfType_boxed_2494_ = lean_unbox(v_whnfType_2487_);
v_res_2495_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_type_2483_, v_maxFVars_x3f_2484_, v_k_2485_, v_cleanupAnnotations_boxed_2493_, v_whnfType_boxed_2494_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2496_, lean_object* v_type_2497_, lean_object* v_maxFVars_x3f_2498_, lean_object* v_k_2499_, uint8_t v_cleanupAnnotations_2500_, uint8_t v_whnfType_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v___x_2507_; 
v___x_2507_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_type_2497_, v_maxFVars_x3f_2498_, v_k_2499_, v_cleanupAnnotations_2500_, v_whnfType_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_type_2509_, lean_object* v_maxFVars_x3f_2510_, lean_object* v_k_2511_, lean_object* v_cleanupAnnotations_2512_, lean_object* v_whnfType_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2519_; uint8_t v_whnfType_boxed_2520_; lean_object* v_res_2521_; 
v_cleanupAnnotations_boxed_2519_ = lean_unbox(v_cleanupAnnotations_2512_);
v_whnfType_boxed_2520_ = lean_unbox(v_whnfType_2513_);
v_res_2521_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2508_, v_type_2509_, v_maxFVars_x3f_2510_, v_k_2511_, v_cleanupAnnotations_boxed_2519_, v_whnfType_boxed_2520_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_mvarId_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v___x_2529_; 
v___x_2529_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2522_, v_x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
v_a_2538_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2529_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2529_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_mvarId_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_mvarId_2546_, v_x_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2554_, lean_object* v_mvarId_2555_, lean_object* v_x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_mvarId_2555_, v_x_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2563_, lean_object* v_mvarId_2564_, lean_object* v_x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2563_, v_mvarId_2564_, v_x_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2572_, lean_object* v_msg_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v_fileName_2579_; lean_object* v_fileMap_2580_; lean_object* v_options_2581_; lean_object* v_currRecDepth_2582_; lean_object* v_maxRecDepth_2583_; lean_object* v_ref_2584_; lean_object* v_currNamespace_2585_; lean_object* v_openDecls_2586_; lean_object* v_initHeartbeats_2587_; lean_object* v_maxHeartbeats_2588_; lean_object* v_quotContext_2589_; lean_object* v_currMacroScope_2590_; uint8_t v_diag_2591_; lean_object* v_cancelTk_x3f_2592_; uint8_t v_suppressElabErrors_2593_; lean_object* v_inheritedTraceOptions_2594_; lean_object* v_ref_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_fileName_2579_ = lean_ctor_get(v___y_2576_, 0);
v_fileMap_2580_ = lean_ctor_get(v___y_2576_, 1);
v_options_2581_ = lean_ctor_get(v___y_2576_, 2);
v_currRecDepth_2582_ = lean_ctor_get(v___y_2576_, 3);
v_maxRecDepth_2583_ = lean_ctor_get(v___y_2576_, 4);
v_ref_2584_ = lean_ctor_get(v___y_2576_, 5);
v_currNamespace_2585_ = lean_ctor_get(v___y_2576_, 6);
v_openDecls_2586_ = lean_ctor_get(v___y_2576_, 7);
v_initHeartbeats_2587_ = lean_ctor_get(v___y_2576_, 8);
v_maxHeartbeats_2588_ = lean_ctor_get(v___y_2576_, 9);
v_quotContext_2589_ = lean_ctor_get(v___y_2576_, 10);
v_currMacroScope_2590_ = lean_ctor_get(v___y_2576_, 11);
v_diag_2591_ = lean_ctor_get_uint8(v___y_2576_, sizeof(void*)*14);
v_cancelTk_x3f_2592_ = lean_ctor_get(v___y_2576_, 12);
v_suppressElabErrors_2593_ = lean_ctor_get_uint8(v___y_2576_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2594_ = lean_ctor_get(v___y_2576_, 13);
v_ref_2595_ = l_Lean_replaceRef(v_ref_2572_, v_ref_2584_);
lean_inc_ref(v_inheritedTraceOptions_2594_);
lean_inc(v_cancelTk_x3f_2592_);
lean_inc(v_currMacroScope_2590_);
lean_inc(v_quotContext_2589_);
lean_inc(v_maxHeartbeats_2588_);
lean_inc(v_initHeartbeats_2587_);
lean_inc(v_openDecls_2586_);
lean_inc(v_currNamespace_2585_);
lean_inc(v_maxRecDepth_2583_);
lean_inc(v_currRecDepth_2582_);
lean_inc_ref(v_options_2581_);
lean_inc_ref(v_fileMap_2580_);
lean_inc_ref(v_fileName_2579_);
v___x_2596_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2596_, 0, v_fileName_2579_);
lean_ctor_set(v___x_2596_, 1, v_fileMap_2580_);
lean_ctor_set(v___x_2596_, 2, v_options_2581_);
lean_ctor_set(v___x_2596_, 3, v_currRecDepth_2582_);
lean_ctor_set(v___x_2596_, 4, v_maxRecDepth_2583_);
lean_ctor_set(v___x_2596_, 5, v_ref_2595_);
lean_ctor_set(v___x_2596_, 6, v_currNamespace_2585_);
lean_ctor_set(v___x_2596_, 7, v_openDecls_2586_);
lean_ctor_set(v___x_2596_, 8, v_initHeartbeats_2587_);
lean_ctor_set(v___x_2596_, 9, v_maxHeartbeats_2588_);
lean_ctor_set(v___x_2596_, 10, v_quotContext_2589_);
lean_ctor_set(v___x_2596_, 11, v_currMacroScope_2590_);
lean_ctor_set(v___x_2596_, 12, v_cancelTk_x3f_2592_);
lean_ctor_set(v___x_2596_, 13, v_inheritedTraceOptions_2594_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*14, v_diag_2591_);
lean_ctor_set_uint8(v___x_2596_, sizeof(void*)*14 + 1, v_suppressElabErrors_2593_);
v___x_2597_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2573_, v___y_2574_, v___y_2575_, v___x_2596_, v___y_2577_);
lean_dec_ref(v___x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2598_, lean_object* v_msg_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2598_, v_msg_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_);
lean_dec(v___y_2603_);
lean_dec_ref(v___y_2602_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v_ref_2598_);
return v_res_2605_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
return v___x_2608_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2610_ = lean_unsigned_to_nat(0u);
v___x_2611_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
lean_ctor_set(v___x_2611_, 2, v___x_2610_);
lean_ctor_set(v___x_2611_, 3, v___x_2609_);
lean_ctor_set(v___x_2611_, 4, v___x_2609_);
lean_ctor_set(v___x_2611_, 5, v___x_2609_);
lean_ctor_set(v___x_2611_, 6, v___x_2609_);
lean_ctor_set(v___x_2611_, 7, v___x_2609_);
lean_ctor_set(v___x_2611_, 8, v___x_2609_);
return v___x_2611_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_unsigned_to_nat(32u);
v___x_2613_ = lean_mk_empty_array_with_capacity(v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
return v___x_2614_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2615_ = ((size_t)5ULL);
v___x_2616_ = lean_unsigned_to_nat(0u);
v___x_2617_ = lean_unsigned_to_nat(32u);
v___x_2618_ = lean_mk_empty_array_with_capacity(v___x_2617_);
v___x_2619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2620_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___x_2618_);
lean_ctor_set(v___x_2620_, 2, v___x_2616_);
lean_ctor_set(v___x_2620_, 3, v___x_2616_);
lean_ctor_set_usize(v___x_2620_, 4, v___x_2615_);
return v___x_2620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = lean_box(1);
v___x_2622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2623_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2623_);
lean_ctor_set(v___x_2624_, 1, v___x_2622_);
lean_ctor_set(v___x_2624_, 2, v___x_2621_);
return v___x_2624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2627_ = l_Lean_stringToMessageData(v___x_2626_);
return v___x_2627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2630_ = l_Lean_stringToMessageData(v___x_2629_);
return v___x_2630_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2633_ = l_Lean_stringToMessageData(v___x_2632_);
return v___x_2633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2636_ = l_Lean_stringToMessageData(v___x_2635_);
return v___x_2636_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2639_ = l_Lean_stringToMessageData(v___x_2638_);
return v___x_2639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2642_ = l_Lean_stringToMessageData(v___x_2641_);
return v___x_2642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2645_ = l_Lean_stringToMessageData(v___x_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2646_, lean_object* v_declHint_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; lean_object* v_env_2651_; uint8_t v___x_2652_; 
v___x_2650_ = lean_st_ref_get(v___y_2648_);
v_env_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc_ref(v_env_2651_);
lean_dec(v___x_2650_);
v___x_2652_ = l_Lean_Name_isAnonymous(v_declHint_2647_);
if (v___x_2652_ == 0)
{
uint8_t v_isExporting_2653_; 
v_isExporting_2653_ = lean_ctor_get_uint8(v_env_2651_, sizeof(void*)*8);
if (v_isExporting_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_dec_ref(v_env_2651_);
lean_dec(v_declHint_2647_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_msg_2646_);
return v___x_2654_;
}
else
{
lean_object* v___x_2655_; uint8_t v___x_2656_; 
lean_inc_ref(v_env_2651_);
v___x_2655_ = l_Lean_Environment_setExporting(v_env_2651_, v___x_2652_);
lean_inc(v_declHint_2647_);
lean_inc_ref(v___x_2655_);
v___x_2656_ = l_Lean_Environment_contains(v___x_2655_, v_declHint_2647_, v_isExporting_2653_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
lean_dec_ref(v___x_2655_);
lean_dec_ref(v_env_2651_);
lean_dec(v_declHint_2647_);
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_msg_2646_);
return v___x_2657_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v_c_2663_; lean_object* v___x_2664_; 
v___x_2658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2660_ = l_Lean_Options_empty;
v___x_2661_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2655_);
lean_ctor_set(v___x_2661_, 1, v___x_2658_);
lean_ctor_set(v___x_2661_, 2, v___x_2659_);
lean_ctor_set(v___x_2661_, 3, v___x_2660_);
lean_inc(v_declHint_2647_);
v___x_2662_ = l_Lean_MessageData_ofConstName(v_declHint_2647_, v___x_2652_);
v_c_2663_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2663_, 0, v___x_2661_);
lean_ctor_set(v_c_2663_, 1, v___x_2662_);
v___x_2664_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2651_, v_declHint_2647_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v_env_2651_);
lean_dec(v_declHint_2647_);
v___x_2665_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2665_);
lean_ctor_set(v___x_2666_, 1, v_c_2663_);
v___x_2667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2666_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = l_Lean_MessageData_note(v___x_2668_);
v___x_2670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_msg_2646_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
return v___x_2671_;
}
else
{
lean_object* v_val_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2707_; 
v_val_2672_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2674_ = v___x_2664_;
v_isShared_2675_ = v_isSharedCheck_2707_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_val_2672_);
lean_dec(v___x_2664_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2707_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v_mod_2679_; uint8_t v___x_2680_; 
v___x_2676_ = lean_box(0);
v___x_2677_ = l_Lean_Environment_header(v_env_2651_);
lean_dec_ref(v_env_2651_);
v___x_2678_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2677_);
v_mod_2679_ = lean_array_get(v___x_2676_, v___x_2678_, v_val_2672_);
lean_dec(v_val_2672_);
lean_dec_ref(v___x_2678_);
v___x_2680_ = l_Lean_isPrivateName(v_declHint_2647_);
lean_dec(v_declHint_2647_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v_c_2663_);
v___x_2683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = l_Lean_MessageData_ofName(v_mod_2679_);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2686_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = l_Lean_MessageData_note(v___x_2688_);
v___x_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_msg_2646_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2690_);
v___x_2692_ = v___x_2674_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
else
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v_c_2663_);
v___x_2696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = l_Lean_MessageData_ofName(v_mod_2679_);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2699_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_MessageData_note(v___x_2701_);
v___x_2703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_msg_2646_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2703_);
v___x_2705_ = v___x_2674_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2708_; 
lean_dec_ref(v_env_2651_);
lean_dec(v_declHint_2647_);
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_msg_2646_);
return v___x_2708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2709_, lean_object* v_declHint_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2709_, v_declHint_2710_, v___y_2711_);
lean_dec(v___y_2711_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2714_, lean_object* v_declHint_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2731_; 
v___x_2721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2714_, v_declHint_2715_, v___y_2719_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2731_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2726_ = l_Lean_unknownIdentifierMessageTag;
v___x_2727_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
lean_ctor_set(v___x_2727_, 1, v_a_2722_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2727_);
v___x_2729_ = v___x_2724_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2732_, lean_object* v_declHint_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2732_, v_declHint_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2740_, lean_object* v_msg_2741_, lean_object* v_declHint_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v___x_2748_; lean_object* v_a_2749_; lean_object* v___x_2750_; 
v___x_2748_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2741_, v_declHint_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref(v___x_2748_);
v___x_2750_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2740_, v_a_2749_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2751_, lean_object* v_msg_2752_, lean_object* v_declHint_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2751_, v_msg_2752_, v_declHint_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v_ref_2751_);
return v_res_2759_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2762_ = l_Lean_stringToMessageData(v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2763_, lean_object* v_constName_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v___x_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2770_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2771_ = 0;
lean_inc(v_constName_2764_);
v___x_2772_ = l_Lean_MessageData_ofConstName(v_constName_2764_, v___x_2771_);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2770_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2773_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2763_, v___x_2775_, v_constName_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2777_, lean_object* v_constName_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2777_, v_constName_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v_ref_2777_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_ref_2791_; lean_object* v___x_2792_; 
v_ref_2791_ = lean_ctor_get(v___y_2788_, 5);
v___x_2792_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2791_, v_constName_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___x_2806_; lean_object* v_env_2807_; uint8_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2806_ = lean_st_ref_get(v___y_2804_);
v_env_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc_ref(v_env_2807_);
lean_dec(v___x_2806_);
v___x_2808_ = 0;
lean_inc(v_constName_2800_);
v___x_2809_ = l_Lean_Environment_find_x3f(v_env_2807_, v_constName_2800_, v___x_2808_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
return v___x_2810_;
}
else
{
lean_object* v_val_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec(v_constName_2800_);
v_val_2811_ = lean_ctor_get(v___x_2809_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2809_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2809_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_val_2811_);
lean_dec(v___x_2809_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
lean_ctor_set_tag(v___x_2813_, 0);
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_val_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
return v_res_2825_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2826_, lean_object* v_as_2827_, size_t v_i_2828_, size_t v_stop_2829_){
_start:
{
uint8_t v___x_2830_; 
v___x_2830_ = lean_usize_dec_eq(v_i_2828_, v_stop_2829_);
if (v___x_2830_ == 0)
{
lean_object* v___x_2831_; uint8_t v___x_2832_; 
v___x_2831_ = lean_array_uget_borrowed(v_as_2827_, v_i_2828_);
v___x_2832_ = l_Lean_Expr_isAppOf(v_e_2826_, v___x_2831_);
if (v___x_2832_ == 0)
{
size_t v___x_2833_; size_t v___x_2834_; 
v___x_2833_ = ((size_t)1ULL);
v___x_2834_ = lean_usize_add(v_i_2828_, v___x_2833_);
v_i_2828_ = v___x_2834_;
goto _start;
}
else
{
return v___x_2832_;
}
}
else
{
uint8_t v___x_2836_; 
v___x_2836_ = 0;
return v___x_2836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2837_, lean_object* v_as_2838_, lean_object* v_i_2839_, lean_object* v_stop_2840_){
_start:
{
size_t v_i_boxed_2841_; size_t v_stop_boxed_2842_; uint8_t v_res_2843_; lean_object* v_r_2844_; 
v_i_boxed_2841_ = lean_unbox_usize(v_i_2839_);
lean_dec(v_i_2839_);
v_stop_boxed_2842_ = lean_unbox_usize(v_stop_2840_);
lean_dec(v_stop_2840_);
v_res_2843_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2837_, v_as_2838_, v_i_boxed_2841_, v_stop_boxed_2842_);
lean_dec_ref(v_as_2838_);
lean_dec_ref(v_e_2837_);
v_r_2844_ = lean_box(v_res_2843_);
return v_r_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2845_, lean_object* v_name_2846_, lean_object* v_levels_2847_, lean_object* v_params_2848_, lean_object* v___y_2849_, lean_object* v___x_2850_, lean_object* v_e_2851_){
_start:
{
uint8_t v___x_2852_; 
v___x_2852_ = l_Lean_Expr_isApp(v_e_2851_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref(v_e_2851_);
lean_dec_ref(v_params_2848_);
lean_dec(v_levels_2847_);
lean_dec(v_name_2846_);
lean_dec(v_numParams_2845_);
v___x_2853_ = lean_box(0);
return v___x_2853_;
}
else
{
lean_object* v_dummy_2854_; lean_object* v_nargs_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___y_2863_; uint8_t v___x_2873_; 
v_dummy_2854_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2855_ = l_Lean_Expr_getAppNumArgs(v_e_2851_);
lean_inc(v_nargs_2855_);
v___x_2856_ = lean_mk_array(v_nargs_2855_, v_dummy_2854_);
v___x_2857_ = lean_unsigned_to_nat(1u);
v___x_2858_ = lean_nat_sub(v_nargs_2855_, v___x_2857_);
lean_dec(v_nargs_2855_);
lean_inc_ref(v_e_2851_);
v___x_2859_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2851_, v___x_2856_, v___x_2858_);
v___x_2860_ = lean_array_get_size(v___x_2859_);
v___x_2861_ = l_Array_toSubarray___redArg(v___x_2859_, v_numParams_2845_, v___x_2860_);
v___x_2873_ = l_Lean_Expr_isAppOf(v_e_2851_, v_name_2846_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; uint8_t v___x_2875_; 
lean_dec(v_name_2846_);
v___x_2874_ = lean_array_get_size(v___y_2849_);
v___x_2875_ = lean_nat_dec_lt(v___x_2850_, v___x_2874_);
if (v___x_2875_ == 0)
{
v___y_2863_ = v___x_2873_;
goto v___jp_2862_;
}
else
{
if (v___x_2875_ == 0)
{
v___y_2863_ = v___x_2873_;
goto v___jp_2862_;
}
else
{
size_t v___x_2876_; size_t v___x_2877_; uint8_t v___x_2878_; 
v___x_2876_ = ((size_t)0ULL);
v___x_2877_ = lean_usize_of_nat(v___x_2874_);
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2851_, v___y_2849_, v___x_2876_, v___x_2877_);
v___y_2863_ = v___x_2878_;
goto v___jp_2862_;
}
}
}
else
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec_ref(v_e_2851_);
v___x_2879_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2846_);
v___x_2880_ = l_Lean_mkConst(v___x_2879_, v_levels_2847_);
v___x_2881_ = l_Subarray_copy___redArg(v___x_2861_);
v___x_2882_ = l_Array_append___redArg(v_params_2848_, v___x_2881_);
lean_dec_ref(v___x_2881_);
v___x_2883_ = l_Lean_mkAppN(v___x_2880_, v___x_2882_);
lean_dec_ref(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
v___jp_2862_:
{
if (v___y_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec_ref(v___x_2861_);
lean_dec_ref(v_e_2851_);
lean_dec_ref(v_params_2848_);
lean_dec(v_levels_2847_);
v___x_2864_ = lean_box(0);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2865_ = l_Lean_Expr_getAppFn(v_e_2851_);
lean_dec_ref(v_e_2851_);
v___x_2866_ = l_Lean_Expr_constName(v___x_2865_);
lean_dec_ref(v___x_2865_);
v___x_2867_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2866_);
v___x_2868_ = l_Lean_mkConst(v___x_2867_, v_levels_2847_);
v___x_2869_ = l_Subarray_copy___redArg(v___x_2861_);
v___x_2870_ = l_Array_append___redArg(v_params_2848_, v___x_2869_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2885_, lean_object* v_name_2886_, lean_object* v_levels_2887_, lean_object* v_params_2888_, lean_object* v___y_2889_, lean_object* v___x_2890_, lean_object* v_e_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2885_, v_name_2886_, v_levels_2887_, v_params_2888_, v___y_2889_, v___x_2890_, v_e_2891_);
lean_dec(v___x_2890_);
lean_dec_ref(v___y_2889_);
return v_res_2892_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__0));
v___x_2895_ = l_Lean_stringToMessageData(v___x_2894_);
return v___x_2895_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__9));
v___x_2918_ = l_Lean_stringToMessageData(v___x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(lean_object* v___x_2919_, lean_object* v___x_2920_, uint8_t v___x_2921_, lean_object* v___x_2922_, lean_object* v___x_2923_, uint8_t v___x_2924_, lean_object* v___x_2925_, lean_object* v_params_2926_, lean_object* v_args_2927_, lean_object* v_indices_2928_, uint8_t v___x_2929_, lean_object* v___x_2930_, lean_object* v_a_2931_, lean_object* v___x_2932_, lean_object* v_targetArgs_2933_, lean_object* v_x_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; uint8_t v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_targetArgs_2933_);
v___x_2941_ = lean_nat_dec_eq(v___x_2940_, v___x_2919_);
if (v___x_2941_ == 0)
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v___x_2923_);
lean_dec(v___x_2922_);
lean_dec_ref(v___x_2920_);
v___x_2942_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1);
v___x_2943_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_2942_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; 
lean_inc(v___y_2938_);
lean_inc_ref(v___y_2937_);
lean_inc(v___y_2936_);
lean_inc_ref(v___y_2935_);
lean_inc_ref(v___x_2920_);
v___x_2944_ = lean_infer_type(v___x_2920_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
if (lean_obj_tag(v_a_2945_) == 7)
{
lean_object* v_binderType_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_binderType_2946_ = lean_ctor_get(v_a_2945_, 1);
lean_inc_ref(v_binderType_2946_);
lean_dec_ref(v_a_2945_);
v___x_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2947_, 0, v_binderType_2946_);
v___x_2948_ = l_Lean_Meta_mkFreshExprMVar(v___x_2947_, v___x_2921_, v___x_2922_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v___x_2950_ = l_Lean_Expr_mvarId_x21(v_a_2949_);
v___x_2951_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2950_, v___x_2923_, v___x_2924_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref(v___x_2951_);
v___x_2953_ = lean_array_fget_borrowed(v_targetArgs_2933_, v___x_2925_);
lean_inc(v___x_2953_);
v___x_2954_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2952_, v___x_2953_, v___y_2936_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3014_; 
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v___x_2954_, 0);
lean_dec(v_unused_3015_);
v___x_2956_ = v___x_2954_;
v_isShared_2957_ = v_isSharedCheck_3014_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v___x_2954_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_3014_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; lean_object* v___x_2963_; 
v___x_2958_ = l_Lean_Expr_app___override(v___x_2920_, v_a_2949_);
lean_inc_ref(v_params_2926_);
v___x_2959_ = l_Array_append___redArg(v_params_2926_, v_args_2927_);
v___x_2960_ = l_Array_append___redArg(v___x_2959_, v_indices_2928_);
v___x_2961_ = l_Array_append___redArg(v___x_2960_, v_targetArgs_2933_);
v___x_2962_ = 1;
v___x_2963_ = l_Lean_Meta_mkLambdaFVars(v___x_2961_, v___x_2958_, v___x_2929_, v___x_2924_, v___x_2929_, v___x_2924_, v___x_2962_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec_ref(v___x_2961_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref(v___x_2963_);
v___x_2965_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_2964_, v___y_2936_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref(v___x_2965_);
v___x_2967_ = l_Lean_Meta_mkForallFVars(v_params_2926_, v___x_2930_, v___x_2929_, v___x_2924_, v___x_2924_, v___x_2962_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec_ref(v_params_2926_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref(v___x_2967_);
v___x_2969_ = l_Lean_ConstantInfo_levelParams(v_a_2931_);
v___x_2970_ = l_Lean_mkCasesOnName(v___x_2932_);
v___x_2971_ = lean_box(0);
lean_inc(v___x_2970_);
v___x_2972_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_2970_, v___x_2969_, v_a_2968_, v_a_2966_, v___x_2971_, v___y_2938_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc(v_a_2973_);
lean_dec_ref(v___x_2972_);
if (v_isShared_2957_ == 0)
{
lean_ctor_set_tag(v___x_2956_, 1);
lean_ctor_set(v___x_2956_, 0, v_a_2973_);
v___x_2975_ = v___x_2956_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2973_);
v___x_2975_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Lean_addDecl(v___x_2975_, v___x_2929_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
lean_dec_ref(v___x_2976_);
v___x_2977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__8));
v___x_2978_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_2978_, 0, v___x_2970_);
lean_closure_set(v___x_2978_, 1, v___x_2977_);
v___x_2979_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_2979_, 0, lean_box(0));
lean_closure_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = l_Lean_liftCommandElabM___redArg(v___x_2979_, v___x_2924_, v___y_2937_, v___y_2938_);
return v___x_2980_;
}
else
{
lean_dec(v___x_2970_);
return v___x_2976_;
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec(v___x_2970_);
lean_del_object(v___x_2956_);
v_a_2982_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2972_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2972_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_2997_; 
lean_dec(v_a_2966_);
lean_del_object(v___x_2956_);
lean_dec(v___x_2932_);
v_a_2990_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2992_ = v___x_2967_;
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_dec(v___x_2967_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_2997_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2993_ == 0)
{
v___x_2995_ = v___x_2992_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_a_2990_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_del_object(v___x_2956_);
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
v_a_2998_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2965_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2965_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_del_object(v___x_2956_);
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
v_a_3006_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2963_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2963_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
}
else
{
lean_dec(v_a_2949_);
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v___x_2920_);
return v___x_2954_;
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v_a_2949_);
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v___x_2920_);
v_a_3016_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2951_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2951_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v___x_2923_);
lean_dec_ref(v___x_2920_);
v_a_3024_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2948_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2948_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v_a_2945_);
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v___x_2923_);
lean_dec(v___x_2922_);
lean_dec_ref(v___x_2920_);
v___x_3032_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10);
v___x_3033_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3032_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_3033_;
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v_params_2926_);
lean_dec_ref(v___x_2923_);
lean_dec(v___x_2922_);
lean_dec_ref(v___x_2920_);
v_a_3034_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_2944_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_2944_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object** _args){
lean_object* v___x_3042_ = _args[0];
lean_object* v___x_3043_ = _args[1];
lean_object* v___x_3044_ = _args[2];
lean_object* v___x_3045_ = _args[3];
lean_object* v___x_3046_ = _args[4];
lean_object* v___x_3047_ = _args[5];
lean_object* v___x_3048_ = _args[6];
lean_object* v_params_3049_ = _args[7];
lean_object* v_args_3050_ = _args[8];
lean_object* v_indices_3051_ = _args[9];
lean_object* v___x_3052_ = _args[10];
lean_object* v___x_3053_ = _args[11];
lean_object* v_a_3054_ = _args[12];
lean_object* v___x_3055_ = _args[13];
lean_object* v_targetArgs_3056_ = _args[14];
lean_object* v_x_3057_ = _args[15];
lean_object* v___y_3058_ = _args[16];
lean_object* v___y_3059_ = _args[17];
lean_object* v___y_3060_ = _args[18];
lean_object* v___y_3061_ = _args[19];
lean_object* v___y_3062_ = _args[20];
_start:
{
uint8_t v___x_13949__boxed_3063_; uint8_t v___x_13952__boxed_3064_; uint8_t v___x_13954__boxed_3065_; lean_object* v_res_3066_; 
v___x_13949__boxed_3063_ = lean_unbox(v___x_3044_);
v___x_13952__boxed_3064_ = lean_unbox(v___x_3047_);
v___x_13954__boxed_3065_ = lean_unbox(v___x_3052_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_3042_, v___x_3043_, v___x_13949__boxed_3063_, v___x_3045_, v___x_3046_, v___x_13952__boxed_3064_, v___x_3048_, v_params_3049_, v_args_3050_, v_indices_3051_, v___x_13954__boxed_3065_, v___x_3053_, v_a_3054_, v___x_3055_, v_targetArgs_3056_, v_x_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_);
lean_dec(v___y_3061_);
lean_dec_ref(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v_x_3057_);
lean_dec_ref(v_targetArgs_3056_);
lean_dec_ref(v_a_3054_);
lean_dec_ref(v_indices_3051_);
lean_dec_ref(v_args_3050_);
lean_dec(v___x_3048_);
lean_dec(v___x_3042_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v___x_3067_, lean_object* v___x_3068_, uint8_t v___x_3069_, lean_object* v___x_3070_, lean_object* v___x_3071_, uint8_t v___x_3072_, lean_object* v___x_3073_, lean_object* v_params_3074_, lean_object* v_args_3075_, uint8_t v___x_3076_, lean_object* v___x_3077_, lean_object* v_a_3078_, lean_object* v___x_3079_, lean_object* v___x_3080_, lean_object* v_indices_3081_, lean_object* v_goalType_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___f_3092_; lean_object* v___x_3093_; 
v___x_3088_ = l_Lean_mkAppN(v___x_3067_, v_indices_3081_);
v___x_3089_ = lean_box(v___x_3069_);
v___x_3090_ = lean_box(v___x_3072_);
v___x_3091_ = lean_box(v___x_3076_);
v___f_3092_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed), 21, 14);
lean_closure_set(v___f_3092_, 0, v___x_3068_);
lean_closure_set(v___f_3092_, 1, v___x_3088_);
lean_closure_set(v___f_3092_, 2, v___x_3089_);
lean_closure_set(v___f_3092_, 3, v___x_3070_);
lean_closure_set(v___f_3092_, 4, v___x_3071_);
lean_closure_set(v___f_3092_, 5, v___x_3090_);
lean_closure_set(v___f_3092_, 6, v___x_3073_);
lean_closure_set(v___f_3092_, 7, v_params_3074_);
lean_closure_set(v___f_3092_, 8, v_args_3075_);
lean_closure_set(v___f_3092_, 9, v_indices_3081_);
lean_closure_set(v___f_3092_, 10, v___x_3091_);
lean_closure_set(v___f_3092_, 11, v___x_3077_);
lean_closure_set(v___f_3092_, 12, v_a_3078_);
lean_closure_set(v___f_3092_, 13, v___x_3079_);
v___x_3093_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_goalType_3082_, v___x_3080_, v___f_3092_, v___x_3076_, v___x_3076_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object** _args){
lean_object* v___x_3094_ = _args[0];
lean_object* v___x_3095_ = _args[1];
lean_object* v___x_3096_ = _args[2];
lean_object* v___x_3097_ = _args[3];
lean_object* v___x_3098_ = _args[4];
lean_object* v___x_3099_ = _args[5];
lean_object* v___x_3100_ = _args[6];
lean_object* v_params_3101_ = _args[7];
lean_object* v_args_3102_ = _args[8];
lean_object* v___x_3103_ = _args[9];
lean_object* v___x_3104_ = _args[10];
lean_object* v_a_3105_ = _args[11];
lean_object* v___x_3106_ = _args[12];
lean_object* v___x_3107_ = _args[13];
lean_object* v_indices_3108_ = _args[14];
lean_object* v_goalType_3109_ = _args[15];
lean_object* v___y_3110_ = _args[16];
lean_object* v___y_3111_ = _args[17];
lean_object* v___y_3112_ = _args[18];
lean_object* v___y_3113_ = _args[19];
lean_object* v___y_3114_ = _args[20];
_start:
{
uint8_t v___x_14237__boxed_3115_; uint8_t v___x_14240__boxed_3116_; uint8_t v___x_14242__boxed_3117_; lean_object* v_res_3118_; 
v___x_14237__boxed_3115_ = lean_unbox(v___x_3096_);
v___x_14240__boxed_3116_ = lean_unbox(v___x_3099_);
v___x_14242__boxed_3117_ = lean_unbox(v___x_3103_);
v_res_3118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v___x_3094_, v___x_3095_, v___x_14237__boxed_3115_, v___x_3097_, v___x_3098_, v___x_14240__boxed_3116_, v___x_3100_, v_params_3101_, v_args_3102_, v___x_14242__boxed_3117_, v___x_3104_, v_a_3105_, v___x_3106_, v___x_3107_, v_indices_3108_, v_goalType_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
return v_res_3118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_3119_, uint8_t v___x_3120_, lean_object* v_snd_3121_, lean_object* v___x_3122_, uint8_t v___x_3123_, lean_object* v___x_3124_, lean_object* v___x_3125_, lean_object* v_a_3126_, lean_object* v___x_3127_, uint8_t v___x_3128_, lean_object* v___x_3129_, lean_object* v___x_3130_, lean_object* v_params_3131_, lean_object* v_args_3132_, lean_object* v___x_3133_, lean_object* v_a_3134_, lean_object* v___x_3135_, lean_object* v___x_3136_, lean_object* v_numIndices_3137_, lean_object* v_goalType_3138_, lean_object* v___x_3139_, lean_object* v___x_3140_, lean_object* v_fst_3141_, lean_object* v___x_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v_lctx_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; 
v_lctx_3148_ = lean_ctor_get(v___y_3143_, 2);
lean_inc(v___x_3119_);
lean_inc_ref(v_lctx_3148_);
v___x_3149_ = l_Lean_LocalContext_get_x21(v_lctx_3148_, v___x_3119_);
v___x_3150_ = l_Lean_LocalDecl_type(v___x_3149_);
lean_dec_ref(v___x_3149_);
v___x_3151_ = 2;
v___x_3152_ = lean_box(0);
v___x_3153_ = 0;
v___x_3154_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3154_, 0, v___x_3152_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*1, v___x_3151_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*1 + 1, v___x_3120_);
lean_ctor_set_uint8(v___x_3154_, sizeof(void*)*1 + 2, v___x_3153_);
lean_inc_ref(v___x_3122_);
lean_inc(v_snd_3121_);
v___x_3155_ = l_Lean_MVarId_rewrite(v_snd_3121_, v___x_3150_, v___x_3122_, v___x_3120_, v___x_3154_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3155_) == 0)
{
lean_object* v_a_3156_; lean_object* v_eNew_3157_; lean_object* v_eqProof_3158_; lean_object* v___x_3159_; 
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref(v___x_3155_);
v_eNew_3157_ = lean_ctor_get(v_a_3156_, 0);
lean_inc_ref(v_eNew_3157_);
v_eqProof_3158_ = lean_ctor_get(v_a_3156_, 1);
lean_inc_ref(v_eqProof_3158_);
lean_dec(v_a_3156_);
v___x_3159_ = l___private_Lean_Meta_Tactic_Replace_0__Lean_Meta_replaceLocalDeclCore(v_snd_3121_, v___x_3119_, v_eNew_3157_, v_eqProof_3158_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___y_3162_; uint8_t v___x_3190_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v___x_3190_ = lean_nat_dec_lt(v___x_3139_, v___x_3140_);
if (v___x_3190_ == 0)
{
v___y_3162_ = v_fst_3141_;
goto v___jp_3161_;
}
else
{
lean_object* v_fvarId_3191_; lean_object* v_xs_x27_3192_; lean_object* v___x_3193_; 
v_fvarId_3191_ = lean_ctor_get(v_a_3160_, 0);
v_xs_x27_3192_ = lean_array_fset(v_fst_3141_, v___x_3139_, v___x_3142_);
lean_inc(v_fvarId_3191_);
v___x_3193_ = lean_array_fset(v_xs_x27_3192_, v___x_3139_, v_fvarId_3191_);
v___y_3162_ = v___x_3193_;
goto v___jp_3161_;
}
v___jp_3161_:
{
lean_object* v_mvarId_3163_; lean_object* v___x_3164_; 
v_mvarId_3163_ = lean_ctor_get(v_a_3160_, 1);
lean_inc(v_mvarId_3163_);
lean_dec(v_a_3160_);
v___x_3164_ = l_Lean_MVarId_revert(v_mvarId_3163_, v___y_3162_, v___x_3123_, v___x_3123_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v_snd_3166_; lean_object* v___x_3167_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v_snd_3166_ = lean_ctor_get(v_a_3165_, 1);
lean_inc(v_snd_3166_);
lean_dec(v_a_3165_);
v___x_3167_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3166_, v___x_3124_, v___y_3144_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3180_; 
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3167_, 0);
lean_dec(v_unused_3181_);
v___x_3169_ = v___x_3167_;
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
else
{
lean_dec(v___x_3167_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___f_3175_; lean_object* v___x_3177_; 
v___x_3171_ = l_Lean_Expr_app___override(v___x_3125_, v_a_3126_);
v___x_3172_ = lean_box(v___x_3128_);
v___x_3173_ = lean_box(v___x_3120_);
v___x_3174_ = lean_box(v___x_3123_);
v___f_3175_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 21, 14);
lean_closure_set(v___f_3175_, 0, v___x_3171_);
lean_closure_set(v___f_3175_, 1, v___x_3127_);
lean_closure_set(v___f_3175_, 2, v___x_3172_);
lean_closure_set(v___f_3175_, 3, v___x_3129_);
lean_closure_set(v___f_3175_, 4, v___x_3122_);
lean_closure_set(v___f_3175_, 5, v___x_3173_);
lean_closure_set(v___f_3175_, 6, v___x_3130_);
lean_closure_set(v___f_3175_, 7, v_params_3131_);
lean_closure_set(v___f_3175_, 8, v_args_3132_);
lean_closure_set(v___f_3175_, 9, v___x_3174_);
lean_closure_set(v___f_3175_, 10, v___x_3133_);
lean_closure_set(v___f_3175_, 11, v_a_3134_);
lean_closure_set(v___f_3175_, 12, v___x_3135_);
lean_closure_set(v___f_3175_, 13, v___x_3136_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 1);
lean_ctor_set(v___x_3169_, 0, v_numIndices_3137_);
v___x_3177_ = v___x_3169_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_numIndices_3137_);
v___x_3177_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_goalType_3138_, v___x_3177_, v___f_3175_, v___x_3123_, v___x_3123_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec_ref(v___y_3143_);
return v___x_3178_;
}
}
}
else
{
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_goalType_3138_);
lean_dec(v_numIndices_3137_);
lean_dec(v___x_3136_);
lean_dec(v___x_3135_);
lean_dec_ref(v_a_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v_args_3132_);
lean_dec_ref(v_params_3131_);
lean_dec(v___x_3130_);
lean_dec(v___x_3129_);
lean_dec(v___x_3127_);
lean_dec_ref(v_a_3126_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v___x_3122_);
return v___x_3167_;
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_goalType_3138_);
lean_dec(v_numIndices_3137_);
lean_dec(v___x_3136_);
lean_dec(v___x_3135_);
lean_dec_ref(v_a_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v_args_3132_);
lean_dec_ref(v_params_3131_);
lean_dec(v___x_3130_);
lean_dec(v___x_3129_);
lean_dec(v___x_3127_);
lean_dec_ref(v_a_3126_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v___x_3122_);
v_a_3182_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3164_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3164_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_fst_3141_);
lean_dec_ref(v_goalType_3138_);
lean_dec(v_numIndices_3137_);
lean_dec(v___x_3136_);
lean_dec(v___x_3135_);
lean_dec_ref(v_a_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v_args_3132_);
lean_dec_ref(v_params_3131_);
lean_dec(v___x_3130_);
lean_dec(v___x_3129_);
lean_dec(v___x_3127_);
lean_dec_ref(v_a_3126_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v___x_3122_);
v_a_3194_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3159_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3159_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_fst_3141_);
lean_dec_ref(v_goalType_3138_);
lean_dec(v_numIndices_3137_);
lean_dec(v___x_3136_);
lean_dec(v___x_3135_);
lean_dec_ref(v_a_3134_);
lean_dec_ref(v___x_3133_);
lean_dec_ref(v_args_3132_);
lean_dec_ref(v_params_3131_);
lean_dec(v___x_3130_);
lean_dec(v___x_3129_);
lean_dec(v___x_3127_);
lean_dec_ref(v_a_3126_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v___x_3124_);
lean_dec_ref(v___x_3122_);
lean_dec(v_snd_3121_);
lean_dec(v___x_3119_);
v_a_3202_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3155_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3155_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3210_ = _args[0];
lean_object* v___x_3211_ = _args[1];
lean_object* v_snd_3212_ = _args[2];
lean_object* v___x_3213_ = _args[3];
lean_object* v___x_3214_ = _args[4];
lean_object* v___x_3215_ = _args[5];
lean_object* v___x_3216_ = _args[6];
lean_object* v_a_3217_ = _args[7];
lean_object* v___x_3218_ = _args[8];
lean_object* v___x_3219_ = _args[9];
lean_object* v___x_3220_ = _args[10];
lean_object* v___x_3221_ = _args[11];
lean_object* v_params_3222_ = _args[12];
lean_object* v_args_3223_ = _args[13];
lean_object* v___x_3224_ = _args[14];
lean_object* v_a_3225_ = _args[15];
lean_object* v___x_3226_ = _args[16];
lean_object* v___x_3227_ = _args[17];
lean_object* v_numIndices_3228_ = _args[18];
lean_object* v_goalType_3229_ = _args[19];
lean_object* v___x_3230_ = _args[20];
lean_object* v___x_3231_ = _args[21];
lean_object* v_fst_3232_ = _args[22];
lean_object* v___x_3233_ = _args[23];
lean_object* v___y_3234_ = _args[24];
lean_object* v___y_3235_ = _args[25];
lean_object* v___y_3236_ = _args[26];
lean_object* v___y_3237_ = _args[27];
lean_object* v___y_3238_ = _args[28];
_start:
{
uint8_t v___x_14299__boxed_3239_; uint8_t v___x_14302__boxed_3240_; uint8_t v___x_14307__boxed_3241_; lean_object* v_res_3242_; 
v___x_14299__boxed_3239_ = lean_unbox(v___x_3211_);
v___x_14302__boxed_3240_ = lean_unbox(v___x_3214_);
v___x_14307__boxed_3241_ = lean_unbox(v___x_3219_);
v_res_3242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3210_, v___x_14299__boxed_3239_, v_snd_3212_, v___x_3213_, v___x_14302__boxed_3240_, v___x_3215_, v___x_3216_, v_a_3217_, v___x_3218_, v___x_14307__boxed_3241_, v___x_3220_, v___x_3221_, v_params_3222_, v_args_3223_, v___x_3224_, v_a_3225_, v___x_3226_, v___x_3227_, v_numIndices_3228_, v_goalType_3229_, v___x_3230_, v___x_3231_, v_fst_3232_, v___x_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec(v___x_3231_);
lean_dec(v___x_3230_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3243_, lean_object* v_a_3244_, lean_object* v_numIndices_3245_, lean_object* v___x_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v___x_3249_, lean_object* v_params_3250_, lean_object* v___x_3251_, lean_object* v_a_3252_, lean_object* v___x_3253_, lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v_args_3256_, lean_object* v_goalType_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = lean_array_get_size(v_args_3256_);
v___x_3264_ = lean_nat_dec_eq(v___x_3263_, v___x_3243_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec_ref(v_goalType_3257_);
lean_dec_ref(v_args_3256_);
lean_dec(v___x_3254_);
lean_dec(v___x_3253_);
lean_dec_ref(v_a_3252_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v_params_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3248_);
lean_dec(v___x_3246_);
lean_dec(v_numIndices_3245_);
lean_dec(v___x_3243_);
v___x_3265_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__1);
v___x_3266_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3265_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
return v___x_3266_;
}
else
{
if (lean_obj_tag(v_a_3244_) == 7)
{
lean_object* v_binderType_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v_binderType_3267_ = lean_ctor_get(v_a_3244_, 1);
lean_inc_ref(v_binderType_3267_);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v_binderType_3267_);
v___x_3269_ = 0;
v___x_3270_ = lean_box(0);
v___x_3271_ = l_Lean_Meta_mkFreshExprMVar(v___x_3268_, v___x_3269_, v___x_3270_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref(v___x_3271_);
v___x_3273_ = l_Lean_Expr_mvarId_x21(v_a_3272_);
v___x_3274_ = lean_nat_add(v_numIndices_3245_, v___x_3243_);
v___x_3275_ = lean_box(0);
v___x_3276_ = 0;
v___x_3277_ = l_Lean_Meta_introNCore(v___x_3273_, v___x_3274_, v___x_3275_, v___x_3276_, v___x_3276_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v_fst_3279_; lean_object* v_snd_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref(v___x_3277_);
v_fst_3279_ = lean_ctor_get(v_a_3278_, 0);
lean_inc(v_fst_3279_);
v_snd_3280_ = lean_ctor_get(v_a_3278_, 1);
lean_inc_n(v_snd_3280_, 2);
lean_dec(v_a_3278_);
v___x_3281_ = lean_array_fget(v_args_3256_, v___x_3246_);
v___x_3282_ = lean_array_get_size(v_fst_3279_);
v___x_3283_ = lean_nat_sub(v___x_3282_, v___x_3243_);
v___x_3284_ = lean_array_get(v___x_3247_, v_fst_3279_, v___x_3283_);
v___x_3285_ = lean_box(v___x_3264_);
v___x_3286_ = lean_box(v___x_3276_);
v___x_3287_ = lean_box(v___x_3269_);
v___f_3288_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 29, 24);
lean_closure_set(v___f_3288_, 0, v___x_3284_);
lean_closure_set(v___f_3288_, 1, v___x_3285_);
lean_closure_set(v___f_3288_, 2, v_snd_3280_);
lean_closure_set(v___f_3288_, 3, v___x_3248_);
lean_closure_set(v___f_3288_, 4, v___x_3286_);
lean_closure_set(v___f_3288_, 5, v___x_3281_);
lean_closure_set(v___f_3288_, 6, v___x_3249_);
lean_closure_set(v___f_3288_, 7, v_a_3272_);
lean_closure_set(v___f_3288_, 8, v___x_3243_);
lean_closure_set(v___f_3288_, 9, v___x_3287_);
lean_closure_set(v___f_3288_, 10, v___x_3270_);
lean_closure_set(v___f_3288_, 11, v___x_3246_);
lean_closure_set(v___f_3288_, 12, v_params_3250_);
lean_closure_set(v___f_3288_, 13, v_args_3256_);
lean_closure_set(v___f_3288_, 14, v___x_3251_);
lean_closure_set(v___f_3288_, 15, v_a_3252_);
lean_closure_set(v___f_3288_, 16, v___x_3253_);
lean_closure_set(v___f_3288_, 17, v___x_3254_);
lean_closure_set(v___f_3288_, 18, v_numIndices_3245_);
lean_closure_set(v___f_3288_, 19, v_goalType_3257_);
lean_closure_set(v___f_3288_, 20, v___x_3283_);
lean_closure_set(v___f_3288_, 21, v___x_3282_);
lean_closure_set(v___f_3288_, 22, v_fst_3279_);
lean_closure_set(v___f_3288_, 23, v___x_3255_);
v___x_3289_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_snd_3280_, v___f_3288_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
return v___x_3289_;
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_a_3272_);
lean_dec_ref(v_goalType_3257_);
lean_dec_ref(v_args_3256_);
lean_dec(v___x_3254_);
lean_dec(v___x_3253_);
lean_dec_ref(v_a_3252_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v_params_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3248_);
lean_dec(v___x_3246_);
lean_dec(v_numIndices_3245_);
lean_dec(v___x_3243_);
v_a_3290_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3277_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3277_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v_goalType_3257_);
lean_dec_ref(v_args_3256_);
lean_dec(v___x_3254_);
lean_dec(v___x_3253_);
lean_dec_ref(v_a_3252_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v_params_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3248_);
lean_dec(v___x_3246_);
lean_dec(v_numIndices_3245_);
lean_dec(v___x_3243_);
v_a_3298_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3271_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3271_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
lean_dec_ref(v_goalType_3257_);
lean_dec_ref(v_args_3256_);
lean_dec(v___x_3254_);
lean_dec(v___x_3253_);
lean_dec_ref(v_a_3252_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v_params_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v___x_3248_);
lean_dec(v___x_3246_);
lean_dec(v_numIndices_3245_);
lean_dec(v___x_3243_);
v___x_3306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___closed__10);
v___x_3307_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3306_, v___y_3258_, v___y_3259_, v___y_3260_, v___y_3261_);
return v___x_3307_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3308_ = _args[0];
lean_object* v_a_3309_ = _args[1];
lean_object* v_numIndices_3310_ = _args[2];
lean_object* v___x_3311_ = _args[3];
lean_object* v___x_3312_ = _args[4];
lean_object* v___x_3313_ = _args[5];
lean_object* v___x_3314_ = _args[6];
lean_object* v_params_3315_ = _args[7];
lean_object* v___x_3316_ = _args[8];
lean_object* v_a_3317_ = _args[9];
lean_object* v___x_3318_ = _args[10];
lean_object* v___x_3319_ = _args[11];
lean_object* v___x_3320_ = _args[12];
lean_object* v_args_3321_ = _args[13];
lean_object* v_goalType_3322_ = _args[14];
lean_object* v___y_3323_ = _args[15];
lean_object* v___y_3324_ = _args[16];
lean_object* v___y_3325_ = _args[17];
lean_object* v___y_3326_ = _args[18];
lean_object* v___y_3327_ = _args[19];
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3308_, v_a_3309_, v_numIndices_3310_, v___x_3311_, v___x_3312_, v___x_3313_, v___x_3314_, v_params_3315_, v___x_3316_, v_a_3317_, v___x_3318_, v___x_3319_, v___x_3320_, v_args_3321_, v_goalType_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___x_3312_);
lean_dec_ref(v_a_3309_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v___x_3335_; lean_object* v_env_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; 
v___x_3335_ = lean_st_ref_get(v___y_3333_);
v_env_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc_ref(v_env_3336_);
lean_dec(v___x_3335_);
v___x_3337_ = 0;
lean_inc(v_constName_3329_);
v___x_3338_ = l_Lean_Environment_findConstVal_x3f(v_env_3336_, v_constName_3329_, v___x_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
return v___x_3339_;
}
else
{
lean_object* v_val_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec(v_constName_3329_);
v_val_3340_ = lean_ctor_get(v___x_3338_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3338_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_val_3340_);
lean_dec(v___x_3338_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
lean_ctor_set_tag(v___x_3342_, 0);
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_val_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3348_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; 
lean_inc(v_constName_3355_);
v___x_3361_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3373_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3373_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3373_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v_levelParams_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; 
v_levelParams_3366_ = lean_ctor_get(v_a_3362_, 1);
lean_inc(v_levelParams_3366_);
lean_dec(v_a_3362_);
v___x_3367_ = lean_box(0);
v___x_3368_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3366_, v___x_3367_);
v___x_3369_ = l_Lean_mkConst(v_constName_3355_, v___x_3368_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3369_);
v___x_3371_ = v___x_3364_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
lean_dec(v_constName_3355_);
v_a_3374_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3376_ = v___x_3361_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_inc(v_a_3374_);
lean_dec(v___x_3361_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3374_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v_levels_3391_, lean_object* v_params_3392_, lean_object* v___y_3393_, lean_object* v_predicates_3394_, lean_object* v_as_3395_, size_t v_sz_3396_, size_t v_i_3397_, lean_object* v_b_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_usize_dec_lt(v_i_3397_, v_sz_3396_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; 
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_params_3392_);
lean_dec(v_levels_3391_);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_b_3398_);
return v___x_3405_;
}
else
{
lean_object* v_a_3406_; lean_object* v_toConstantVal_3407_; lean_object* v_numParams_3408_; lean_object* v_numIndices_3409_; lean_object* v_name_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_a_3406_ = lean_array_uget_borrowed(v_as_3395_, v_i_3397_);
v_toConstantVal_3407_ = lean_ctor_get(v_a_3406_, 0);
v_numParams_3408_ = lean_ctor_get(v_a_3406_, 1);
v_numIndices_3409_ = lean_ctor_get(v_a_3406_, 2);
v_name_3410_ = lean_ctor_get(v_toConstantVal_3407_, 0);
lean_inc(v_name_3410_);
v___x_3411_ = l_Lean_mkCasesOnName(v_name_3410_);
lean_inc(v___x_3411_);
v___x_3412_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3411_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref(v___x_3412_);
v___x_3414_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3411_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref(v___x_3414_);
lean_inc_ref(v_params_3392_);
v___x_3416_ = l_Array_append___redArg(v_params_3392_, v_predicates_3394_);
v___x_3417_ = l_Lean_mkAppN(v_a_3415_, v___x_3416_);
lean_dec_ref(v___x_3416_);
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3401_);
lean_inc(v___y_3400_);
lean_inc_ref(v___y_3399_);
lean_inc_ref(v___x_3417_);
v___x_3418_ = lean_infer_type(v___x_3417_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref(v___x_3418_);
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3401_);
lean_inc(v___y_3400_);
lean_inc_ref(v___y_3399_);
lean_inc_ref(v___x_3417_);
v___x_3420_ = lean_infer_type(v___x_3417_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___f_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_box(0);
v___x_3424_ = lean_box(0);
lean_inc_ref(v___y_3393_);
lean_inc_ref_n(v_params_3392_, 2);
lean_inc_n(v_levels_3391_, 2);
lean_inc_n(v_name_3410_, 2);
lean_inc(v_numParams_3408_);
v___f_3425_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3425_, 0, v_numParams_3408_);
lean_closure_set(v___f_3425_, 1, v_name_3410_);
lean_closure_set(v___f_3425_, 2, v_levels_3391_);
lean_closure_set(v___f_3425_, 3, v_params_3392_);
lean_closure_set(v___f_3425_, 4, v___y_3393_);
lean_closure_set(v___f_3425_, 5, v___x_3422_);
v___x_3426_ = lean_replace_expr(v___f_3425_, v_a_3419_);
lean_dec(v_a_3419_);
lean_dec_ref(v___f_3425_);
v___x_3427_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3410_);
v___x_3428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3427_);
v___x_3429_ = l_Lean_Name_append(v___x_3427_, v___x_3428_);
v___x_3430_ = l_Lean_mkConst(v___x_3429_, v_levels_3391_);
v___x_3431_ = lean_unsigned_to_nat(1u);
v___x_3432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3426_);
lean_inc(v_numIndices_3409_);
v___f_3433_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 20, 13);
lean_closure_set(v___f_3433_, 0, v___x_3431_);
lean_closure_set(v___f_3433_, 1, v_a_3421_);
lean_closure_set(v___f_3433_, 2, v_numIndices_3409_);
lean_closure_set(v___f_3433_, 3, v___x_3422_);
lean_closure_set(v___f_3433_, 4, v___x_3423_);
lean_closure_set(v___f_3433_, 5, v___x_3430_);
lean_closure_set(v___f_3433_, 6, v___x_3417_);
lean_closure_set(v___f_3433_, 7, v_params_3392_);
lean_closure_set(v___f_3433_, 8, v___x_3426_);
lean_closure_set(v___f_3433_, 9, v_a_3413_);
lean_closure_set(v___f_3433_, 10, v___x_3427_);
lean_closure_set(v___f_3433_, 11, v___x_3432_);
lean_closure_set(v___f_3433_, 12, v___x_3424_);
v___x_3434_ = 0;
v___x_3435_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v___x_3426_, v___x_3432_, v___f_3433_, v___x_3434_, v___x_3434_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
if (lean_obj_tag(v___x_3435_) == 0)
{
size_t v___x_3436_; size_t v___x_3437_; 
lean_dec_ref(v___x_3435_);
v___x_3436_ = ((size_t)1ULL);
v___x_3437_ = lean_usize_add(v_i_3397_, v___x_3436_);
v_i_3397_ = v___x_3437_;
v_b_3398_ = v___x_3424_;
goto _start;
}
else
{
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_params_3392_);
lean_dec(v_levels_3391_);
return v___x_3435_;
}
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3446_; 
lean_dec(v_a_3419_);
lean_dec_ref(v___x_3417_);
lean_dec(v_a_3413_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_params_3392_);
lean_dec(v_levels_3391_);
v_a_3439_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3441_ = v___x_3420_;
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v___x_3420_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3446_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v___x_3417_);
lean_dec(v_a_3413_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_params_3392_);
lean_dec(v_levels_3391_);
v_a_3447_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3418_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3418_);
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
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_dec(v_a_3413_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_params_3392_);
lean_dec(v_levels_3391_);
v_a_3455_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3414_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3414_);
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
lean_dec(v___x_3411_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_params_3392_);
lean_dec(v_levels_3391_);
v_a_3463_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3412_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3412_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v_levels_3471_, lean_object* v_params_3472_, lean_object* v___y_3473_, lean_object* v_predicates_3474_, lean_object* v_as_3475_, lean_object* v_sz_3476_, lean_object* v_i_3477_, lean_object* v_b_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
size_t v_sz_boxed_3484_; size_t v_i_boxed_3485_; lean_object* v_res_3486_; 
v_sz_boxed_3484_ = lean_unbox_usize(v_sz_3476_);
lean_dec(v_sz_3476_);
v_i_boxed_3485_ = lean_unbox_usize(v_i_3477_);
lean_dec(v_i_3477_);
v_res_3486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3471_, v_params_3472_, v___y_3473_, v_predicates_3474_, v_as_3475_, v_sz_boxed_3484_, v_i_boxed_3485_, v_b_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec_ref(v_as_3475_);
lean_dec_ref(v_predicates_3474_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3487_, size_t v_sz_3488_, size_t v_i_3489_, lean_object* v_bs_3490_){
_start:
{
uint8_t v___x_3491_; 
v___x_3491_ = lean_usize_dec_lt(v_i_3489_, v_sz_3488_);
if (v___x_3491_ == 0)
{
lean_dec(v_levels_3487_);
return v_bs_3490_;
}
else
{
lean_object* v_v_3492_; lean_object* v_toConstantVal_3493_; lean_object* v_name_3494_; lean_object* v___x_3495_; lean_object* v_bs_x27_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v_v_3492_ = lean_array_uget_borrowed(v_bs_3490_, v_i_3489_);
v_toConstantVal_3493_ = lean_ctor_get(v_v_3492_, 0);
v_name_3494_ = lean_ctor_get(v_toConstantVal_3493_, 0);
lean_inc(v_name_3494_);
v___x_3495_ = lean_unsigned_to_nat(0u);
v_bs_x27_3496_ = lean_array_uset(v_bs_3490_, v_i_3489_, v___x_3495_);
v___x_3497_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3494_);
lean_inc(v_levels_3487_);
v___x_3498_ = l_Lean_mkConst(v___x_3497_, v_levels_3487_);
v___x_3499_ = ((size_t)1ULL);
v___x_3500_ = lean_usize_add(v_i_3489_, v___x_3499_);
v___x_3501_ = lean_array_uset(v_bs_x27_3496_, v_i_3489_, v___x_3498_);
v_i_3489_ = v___x_3500_;
v_bs_3490_ = v___x_3501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3503_, lean_object* v_sz_3504_, lean_object* v_i_3505_, lean_object* v_bs_3506_){
_start:
{
size_t v_sz_boxed_3507_; size_t v_i_boxed_3508_; lean_object* v_res_3509_; 
v_sz_boxed_3507_ = lean_unbox_usize(v_sz_3504_);
lean_dec(v_sz_3504_);
v_i_boxed_3508_ = lean_unbox_usize(v_i_3505_);
lean_dec(v_i_3505_);
v_res_3509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3503_, v_sz_boxed_3507_, v_i_boxed_3508_, v_bs_3506_);
return v_res_3509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3510_, lean_object* v_levels_3511_, lean_object* v___y_3512_, lean_object* v_params_3513_, lean_object* v_x_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
size_t v_sz_3520_; size_t v___x_3521_; lean_object* v_predicates_3522_; size_t v_sz_3523_; lean_object* v_predicates_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_sz_3520_ = lean_array_size(v_infos_3510_);
v___x_3521_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3510_);
lean_inc(v_levels_3511_);
v_predicates_3522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3511_, v_sz_3520_, v___x_3521_, v_infos_3510_);
v_sz_3523_ = lean_array_size(v_predicates_3522_);
v_predicates_3524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3513_, v_sz_3523_, v___x_3521_, v_predicates_3522_);
v___x_3525_ = lean_box(0);
v___x_3526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3511_, v_params_3513_, v___y_3512_, v_predicates_3524_, v_infos_3510_, v_sz_3520_, v___x_3521_, v___x_3525_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_);
lean_dec_ref(v_infos_3510_);
lean_dec_ref(v_predicates_3524_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3533_ == 0)
{
lean_object* v_unused_3534_; 
v_unused_3534_ = lean_ctor_get(v___x_3526_, 0);
lean_dec(v_unused_3534_);
v___x_3528_ = v___x_3526_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_dec(v___x_3526_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3525_);
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3525_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
else
{
return v___x_3526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3535_, lean_object* v_levels_3536_, lean_object* v___y_3537_, lean_object* v_params_3538_, lean_object* v_x_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3535_, v_levels_3536_, v___y_3537_, v_params_3538_, v_x_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v_x_3539_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3546_, size_t v_i_3547_, size_t v_stop_3548_, lean_object* v_b_3549_){
_start:
{
uint8_t v___x_3550_; 
v___x_3550_ = lean_usize_dec_eq(v_i_3547_, v_stop_3548_);
if (v___x_3550_ == 0)
{
lean_object* v___x_3551_; lean_object* v_ctors_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; size_t v___x_3555_; size_t v___x_3556_; 
v___x_3551_ = lean_array_uget_borrowed(v_as_3546_, v_i_3547_);
v_ctors_3552_ = lean_ctor_get(v___x_3551_, 4);
lean_inc(v_ctors_3552_);
v___x_3553_ = lean_array_mk(v_ctors_3552_);
v___x_3554_ = l_Array_append___redArg(v_b_3549_, v___x_3553_);
lean_dec_ref(v___x_3553_);
v___x_3555_ = ((size_t)1ULL);
v___x_3556_ = lean_usize_add(v_i_3547_, v___x_3555_);
v_i_3547_ = v___x_3556_;
v_b_3549_ = v___x_3554_;
goto _start;
}
else
{
return v_b_3549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3558_, lean_object* v_i_3559_, lean_object* v_stop_3560_, lean_object* v_b_3561_){
_start:
{
size_t v_i_boxed_3562_; size_t v_stop_boxed_3563_; lean_object* v_res_3564_; 
v_i_boxed_3562_ = lean_unbox_usize(v_i_3559_);
lean_dec(v_i_3559_);
v_stop_boxed_3563_ = lean_unbox_usize(v_stop_3560_);
lean_dec(v_stop_3560_);
v_res_3564_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3558_, v_i_boxed_3562_, v_stop_boxed_3563_, v_b_3561_);
lean_dec_ref(v_as_3558_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v_toConstantVal_3576_; lean_object* v_numParams_3577_; lean_object* v_levelParams_3578_; lean_object* v_type_3579_; lean_object* v___x_3580_; lean_object* v_levels_3581_; lean_object* v___y_3583_; lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3573_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3574_ = lean_unsigned_to_nat(0u);
v___x_3575_ = lean_array_get_borrowed(v___x_3573_, v_infos_3567_, v___x_3574_);
v_toConstantVal_3576_ = lean_ctor_get(v___x_3575_, 0);
v_numParams_3577_ = lean_ctor_get(v___x_3575_, 1);
lean_inc(v_numParams_3577_);
v_levelParams_3578_ = lean_ctor_get(v_toConstantVal_3576_, 1);
v_type_3579_ = lean_ctor_get(v_toConstantVal_3576_, 2);
lean_inc_ref(v_type_3579_);
v___x_3580_ = lean_box(0);
lean_inc(v_levelParams_3578_);
v_levels_3581_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3578_, v___x_3580_);
v___x_3590_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3591_ = lean_array_get_size(v_infos_3567_);
v___x_3592_ = lean_nat_dec_lt(v___x_3574_, v___x_3591_);
if (v___x_3592_ == 0)
{
v___y_3583_ = v___x_3590_;
goto v___jp_3582_;
}
else
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_nat_dec_le(v___x_3591_, v___x_3591_);
if (v___x_3593_ == 0)
{
if (v___x_3592_ == 0)
{
v___y_3583_ = v___x_3590_;
goto v___jp_3582_;
}
else
{
size_t v___x_3594_; size_t v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = lean_usize_of_nat(v___x_3591_);
v___x_3596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3567_, v___x_3594_, v___x_3595_, v___x_3590_);
v___y_3583_ = v___x_3596_;
goto v___jp_3582_;
}
}
else
{
size_t v___x_3597_; size_t v___x_3598_; lean_object* v___x_3599_; 
v___x_3597_ = ((size_t)0ULL);
v___x_3598_ = lean_usize_of_nat(v___x_3591_);
v___x_3599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3567_, v___x_3597_, v___x_3598_, v___x_3590_);
v___y_3583_ = v___x_3599_;
goto v___jp_3582_;
}
}
v___jp_3582_:
{
lean_object* v___f_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; 
lean_inc_ref(v_infos_3567_);
v___f_3584_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3584_, 0, v_infos_3567_);
lean_closure_set(v___f_3584_, 1, v_levels_3581_);
lean_closure_set(v___f_3584_, 2, v___y_3583_);
v___x_3585_ = lean_array_get_size(v_infos_3567_);
lean_dec_ref(v_infos_3567_);
v___x_3586_ = lean_nat_sub(v_numParams_3577_, v___x_3585_);
lean_dec(v_numParams_3577_);
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
v___x_3588_ = 0;
v___x_3589_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_type_3579_, v___x_3587_, v___f_3584_, v___x_3588_, v___x_3588_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
return v___x_3589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3607_, lean_object* v_constName_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3615_, lean_object* v_constName_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3615_, v_constName_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3623_, lean_object* v_ref_3624_, lean_object* v_constName_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3624_, v_constName_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_);
return v___x_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3632_, lean_object* v_ref_3633_, lean_object* v_constName_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v_res_3640_; 
v_res_3640_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3632_, v_ref_3633_, v_constName_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_ref_3633_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3641_, lean_object* v_ref_3642_, lean_object* v_msg_3643_, lean_object* v_declHint_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3642_, v_msg_3643_, v_declHint_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3651_, lean_object* v_ref_3652_, lean_object* v_msg_3653_, lean_object* v_declHint_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3651_, v_ref_3652_, v_msg_3653_, v_declHint_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec(v_ref_3652_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3661_, lean_object* v_declHint_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3661_, v_declHint_3662_, v___y_3666_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3669_, lean_object* v_declHint_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3669_, v_declHint_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3677_, lean_object* v_ref_3678_, lean_object* v_msg_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3678_, v_msg_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3686_, lean_object* v_ref_3687_, lean_object* v_msg_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3686_, v_ref_3687_, v_msg_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v_ref_3687_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3698_, lean_object* v___x_3699_, lean_object* v_params_3700_, size_t v_sz_3701_, size_t v_i_3702_, lean_object* v_bs_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_usize_dec_lt(v_i_3702_, v_sz_3701_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v_params_3700_);
lean_dec_ref(v___x_3699_);
lean_dec(v___x_3698_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v_bs_3703_);
return v___x_3710_;
}
else
{
lean_object* v_v_3711_; lean_object* v_toConstantVal_3712_; lean_object* v_name_3713_; lean_object* v___x_3714_; lean_object* v_bs_x27_3715_; lean_object* v___y_3717_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v_v_3711_ = lean_array_uget_borrowed(v_bs_3703_, v_i_3702_);
v_toConstantVal_3712_ = lean_ctor_get(v_v_3711_, 0);
v_name_3713_ = lean_ctor_get(v_toConstantVal_3712_, 0);
lean_inc(v_name_3713_);
v___x_3714_ = lean_unsigned_to_nat(0u);
v_bs_x27_3715_ = lean_array_uset(v_bs_3703_, v_i_3702_, v___x_3714_);
v___x_3731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3732_ = l_Lean_Name_append(v_name_3713_, v___x_3731_);
lean_inc(v___x_3698_);
v___x_3733_ = l_Lean_mkConst(v___x_3732_, v___x_3698_);
v___x_3734_ = l_Lean_Meta_unfoldDefinition(v___x_3733_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; size_t v_sz_3736_; size_t v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; uint8_t v___x_3741_; uint8_t v___x_3742_; lean_object* v___x_3743_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref(v___x_3734_);
v_sz_3736_ = lean_array_size(v___x_3699_);
v___x_3737_ = ((size_t)0ULL);
lean_inc_ref(v___x_3699_);
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3700_, v_sz_3736_, v___x_3737_, v___x_3699_);
lean_inc_ref(v_params_3700_);
v___x_3739_ = l_Array_append___redArg(v_params_3700_, v___x_3738_);
lean_dec_ref(v___x_3738_);
v___x_3740_ = l_Lean_mkAppN(v_a_3735_, v___x_3739_);
lean_dec_ref(v___x_3739_);
v___x_3741_ = 0;
v___x_3742_ = 1;
v___x_3743_ = l_Lean_Meta_mkLambdaFVars(v_params_3700_, v___x_3740_, v___x_3741_, v___x_3709_, v___x_3741_, v___x_3709_, v___x_3742_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
v___y_3717_ = v___x_3743_;
goto v___jp_3716_;
}
else
{
v___y_3717_ = v___x_3734_;
goto v___jp_3716_;
}
v___jp_3716_:
{
if (lean_obj_tag(v___y_3717_) == 0)
{
lean_object* v_a_3718_; size_t v___x_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v_a_3718_ = lean_ctor_get(v___y_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___y_3717_);
v___x_3719_ = ((size_t)1ULL);
v___x_3720_ = lean_usize_add(v_i_3702_, v___x_3719_);
v___x_3721_ = lean_array_uset(v_bs_x27_3715_, v_i_3702_, v_a_3718_);
v_i_3702_ = v___x_3720_;
v_bs_3703_ = v___x_3721_;
goto _start;
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_bs_x27_3715_);
lean_dec_ref(v_params_3700_);
lean_dec_ref(v___x_3699_);
lean_dec(v___x_3698_);
v_a_3723_ = lean_ctor_get(v___y_3717_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___y_3717_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___y_3717_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___y_3717_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3744_, lean_object* v___x_3745_, lean_object* v_params_3746_, lean_object* v_sz_3747_, lean_object* v_i_3748_, lean_object* v_bs_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
size_t v_sz_boxed_3755_; size_t v_i_boxed_3756_; lean_object* v_res_3757_; 
v_sz_boxed_3755_ = lean_unbox_usize(v_sz_3747_);
lean_dec(v_sz_3747_);
v_i_boxed_3756_ = lean_unbox_usize(v_i_3748_);
lean_dec(v_i_3748_);
v_res_3757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3744_, v___x_3745_, v_params_3746_, v_sz_boxed_3755_, v_i_boxed_3756_, v_bs_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3758_, lean_object* v___x_3759_, size_t v_sz_3760_, size_t v___x_3761_, lean_object* v_a_3762_, lean_object* v_params_3763_, lean_object* v_x_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3758_, v___x_3759_, v_params_3763_, v_sz_3760_, v___x_3761_, v_a_3762_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3773_, lean_object* v___x_3774_, lean_object* v_sz_3775_, lean_object* v___x_3776_, lean_object* v_a_3777_, lean_object* v_params_3778_, lean_object* v_x_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
size_t v_sz_boxed_3787_; size_t v___x_5220__boxed_3788_; lean_object* v_res_3789_; 
v_sz_boxed_3787_ = lean_unbox_usize(v_sz_3775_);
lean_dec(v_sz_3775_);
v___x_5220__boxed_3788_ = lean_unbox_usize(v___x_3776_);
lean_dec(v___x_3776_);
v_res_3789_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3773_, v___x_3774_, v_sz_boxed_3787_, v___x_5220__boxed_3788_, v_a_3777_, v_params_3778_, v_x_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec_ref(v_x_3779_);
return v_res_3789_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__0));
v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(lean_object* v_constName_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; lean_object* v_env_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_st_ref_get(v___y_3799_);
v_env_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc_ref(v_env_3802_);
lean_dec(v___x_3801_);
lean_inc(v_constName_3793_);
v___x_3803_ = l_Lean_isInductiveCore_x3f(v_env_3802_, v_constName_3793_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3804_; uint8_t v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3804_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_3805_ = 0;
v___x_3806_ = l_Lean_MessageData_ofConstName(v_constName_3793_, v___x_3805_);
v___x_3807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3804_);
lean_ctor_set(v___x_3807_, 1, v___x_3806_);
v___x_3808_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___closed__1);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_3809_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v___x_3810_;
}
else
{
lean_object* v_val_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec(v_constName_3793_);
v_val_3811_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3803_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_val_3811_);
lean_dec(v___x_3803_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v___x_3816_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 0);
v___x_3816_ = v___x_3813_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_val_3811_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0___boxed(lean_object* v_constName_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v_res_3827_; 
v_res_3827_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_constName_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
lean_dec(v___y_3823_);
lean_dec_ref(v___y_3822_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(size_t v_sz_3828_, size_t v_i_3829_, lean_object* v_bs_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
uint8_t v___x_3838_; 
v___x_3838_ = lean_usize_dec_lt(v_i_3829_, v_sz_3828_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; 
v___x_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3839_, 0, v_bs_3830_);
return v___x_3839_;
}
else
{
lean_object* v_v_3840_; lean_object* v_declName_3841_; lean_object* v___x_3842_; 
v_v_3840_ = lean_array_uget_borrowed(v_bs_3830_, v_i_3829_);
v_declName_3841_ = lean_ctor_get(v_v_3840_, 1);
lean_inc(v_declName_3841_);
v___x_3842_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_3841_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3844_; lean_object* v_bs_x27_3845_; size_t v___x_3846_; size_t v___x_3847_; lean_object* v___x_3848_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref(v___x_3842_);
v___x_3844_ = lean_unsigned_to_nat(0u);
v_bs_x27_3845_ = lean_array_uset(v_bs_3830_, v_i_3829_, v___x_3844_);
v___x_3846_ = ((size_t)1ULL);
v___x_3847_ = lean_usize_add(v_i_3829_, v___x_3846_);
v___x_3848_ = lean_array_uset(v_bs_x27_3845_, v_i_3829_, v_a_3843_);
v_i_3829_ = v___x_3847_;
v_bs_3830_ = v___x_3848_;
goto _start;
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v_bs_3830_);
v_a_3850_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3842_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3842_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1___boxed(lean_object* v_sz_3858_, lean_object* v_i_3859_, lean_object* v_bs_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
size_t v_sz_boxed_3868_; size_t v_i_boxed_3869_; lean_object* v_res_3870_; 
v_sz_boxed_3868_ = lean_unbox_usize(v_sz_3858_);
lean_dec(v_sz_3858_);
v_i_boxed_3869_ = lean_unbox_usize(v_i_3859_);
lean_dec(v_i_3859_);
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_boxed_3868_, v_i_boxed_3869_, v_bs_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3870_;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3871_ = l_Lean_instInhabitedExpr;
v___x_3872_ = lean_box(0);
v___x_3873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
lean_ctor_set(v___x_3873_, 1, v___x_3871_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3874_, lean_object* v_a_3875_, lean_object* v___x_3876_, lean_object* v_as_3877_, lean_object* v_i_3878_, lean_object* v_j_3879_, lean_object* v_bs_3880_){
_start:
{
lean_object* v_zero_3881_; uint8_t v_isZero_3882_; 
v_zero_3881_ = lean_unsigned_to_nat(0u);
v_isZero_3882_ = lean_nat_dec_eq(v_i_3878_, v_zero_3881_);
if (v_isZero_3882_ == 1)
{
lean_dec(v_j_3879_);
lean_dec(v_i_3878_);
lean_dec(v___x_3876_);
return v_bs_3880_;
}
else
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v_ref_3885_; lean_object* v_modifiers_3886_; uint8_t v_isGreatest_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v_fst_3890_; lean_object* v_snd_3891_; lean_object* v_one_3892_; lean_object* v_n_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; uint8_t v___y_3898_; 
v___x_3883_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v___x_3884_ = lean_array_get_borrowed(v___x_3883_, v_coinductiveElabData_3874_, v_j_3879_);
v_ref_3885_ = lean_ctor_get(v___x_3884_, 2);
v_modifiers_3886_ = lean_ctor_get(v___x_3884_, 3);
v_isGreatest_3887_ = lean_ctor_get_uint8(v___x_3884_, sizeof(void*)*5);
v___x_3888_ = lean_obj_once(&l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3889_ = lean_array_get_borrowed(v___x_3888_, v_a_3875_, v_j_3879_);
v_fst_3890_ = lean_ctor_get(v___x_3889_, 0);
v_snd_3891_ = lean_ctor_get(v___x_3889_, 1);
v_one_3892_ = lean_unsigned_to_nat(1u);
v_n_3893_ = lean_nat_sub(v_i_3878_, v_one_3892_);
lean_dec(v_i_3878_);
v___x_3894_ = lean_array_fget_borrowed(v_as_3877_, v_j_3879_);
v___x_3895_ = 0;
v___x_3896_ = lean_box(0);
if (v_isGreatest_3887_ == 0)
{
uint8_t v___x_3906_; 
v___x_3906_ = 2;
v___y_3898_ = v___x_3906_;
goto v___jp_3897_;
}
else
{
uint8_t v___x_3907_; 
v___x_3907_ = 1;
v___y_3898_ = v___x_3907_;
goto v___jp_3897_;
}
v___jp_3897_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_inc_n(v_ref_3885_, 4);
v___x_3899_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3899_, 0, v_ref_3885_);
lean_ctor_set(v___x_3899_, 1, v___x_3896_);
lean_ctor_set_uint8(v___x_3899_, sizeof(void*)*2, v___y_3898_);
v___x_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___x_3899_);
v___x_3901_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3901_, 0, v_ref_3885_);
lean_ctor_set(v___x_3901_, 1, v___x_3896_);
lean_ctor_set(v___x_3901_, 2, v___x_3896_);
lean_ctor_set(v___x_3901_, 3, v___x_3900_);
lean_ctor_set(v___x_3901_, 4, v___x_3896_);
lean_ctor_set(v___x_3901_, 5, v_zero_3881_);
lean_inc(v___x_3894_);
lean_inc(v_snd_3891_);
lean_inc(v_fst_3890_);
lean_inc_ref(v_modifiers_3886_);
lean_inc(v___x_3876_);
v___x_3902_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3902_, 0, v_ref_3885_);
lean_ctor_set(v___x_3902_, 1, v___x_3876_);
lean_ctor_set(v___x_3902_, 2, v_modifiers_3886_);
lean_ctor_set(v___x_3902_, 3, v_fst_3890_);
lean_ctor_set(v___x_3902_, 4, v_ref_3885_);
lean_ctor_set(v___x_3902_, 5, v_zero_3881_);
lean_ctor_set(v___x_3902_, 6, v_snd_3891_);
lean_ctor_set(v___x_3902_, 7, v___x_3894_);
lean_ctor_set(v___x_3902_, 8, v___x_3901_);
lean_ctor_set_uint8(v___x_3902_, sizeof(void*)*9, v___x_3895_);
v___x_3903_ = lean_nat_add(v_j_3879_, v_one_3892_);
lean_dec(v_j_3879_);
v___x_3904_ = lean_array_push(v_bs_3880_, v___x_3902_);
v_i_3878_ = v_n_3893_;
v_j_3879_ = v___x_3903_;
v_bs_3880_ = v___x_3904_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___boxed(lean_object* v_coinductiveElabData_3908_, lean_object* v_a_3909_, lean_object* v___x_3910_, lean_object* v_as_3911_, lean_object* v_i_3912_, lean_object* v_j_3913_, lean_object* v_bs_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_3908_, v_a_3909_, v___x_3910_, v_as_3911_, v_i_3912_, v_j_3913_, v_bs_3914_);
lean_dec_ref(v_as_3911_);
lean_dec_ref(v_a_3909_);
lean_dec_ref(v_coinductiveElabData_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(lean_object* v_a_3916_, lean_object* v_a_3917_){
_start:
{
if (lean_obj_tag(v_a_3916_) == 0)
{
lean_object* v___x_3918_; 
v___x_3918_ = l_List_reverse___redArg(v_a_3917_);
return v___x_3918_;
}
else
{
lean_object* v_head_3919_; lean_object* v_tail_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3929_; 
v_head_3919_ = lean_ctor_get(v_a_3916_, 0);
v_tail_3920_ = lean_ctor_get(v_a_3916_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_a_3916_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3922_ = v_a_3916_;
v_isShared_3923_ = v_isSharedCheck_3929_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_tail_3920_);
lean_inc(v_head_3919_);
lean_dec(v_a_3916_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3929_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3924_ = l_Lean_MessageData_ofName(v_head_3919_);
if (v_isShared_3923_ == 0)
{
lean_ctor_set(v___x_3922_, 1, v_a_3917_);
lean_ctor_set(v___x_3922_, 0, v___x_3924_);
v___x_3926_ = v___x_3922_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3924_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_a_3917_);
v___x_3926_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
v_a_3916_ = v_tail_3920_;
v_a_3917_ = v___x_3926_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(size_t v_sz_3930_, size_t v_i_3931_, lean_object* v_bs_3932_){
_start:
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_usize_dec_lt(v_i_3931_, v_sz_3930_);
if (v___x_3933_ == 0)
{
return v_bs_3932_;
}
else
{
lean_object* v_v_3934_; lean_object* v_declName_3935_; lean_object* v___x_3936_; lean_object* v_bs_x27_3937_; size_t v___x_3938_; size_t v___x_3939_; lean_object* v___x_3940_; 
v_v_3934_ = lean_array_uget_borrowed(v_bs_3932_, v_i_3931_);
v_declName_3935_ = lean_ctor_get(v_v_3934_, 1);
lean_inc(v_declName_3935_);
v___x_3936_ = lean_unsigned_to_nat(0u);
v_bs_x27_3937_ = lean_array_uset(v_bs_3932_, v_i_3931_, v___x_3936_);
v___x_3938_ = ((size_t)1ULL);
v___x_3939_ = lean_usize_add(v_i_3931_, v___x_3938_);
v___x_3940_ = lean_array_uset(v_bs_x27_3937_, v_i_3931_, v_declName_3935_);
v_i_3931_ = v___x_3939_;
v_bs_3932_ = v___x_3940_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6___boxed(lean_object* v_sz_3942_, lean_object* v_i_3943_, lean_object* v_bs_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3942_);
lean_dec(v_sz_3942_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3943_);
lean_dec(v_i_3943_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_boxed_3945_, v_i_boxed_3946_, v_bs_3944_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v_v_3948_, lean_object* v___x_3949_, lean_object* v___x_3950_, uint8_t v___x_3951_, lean_object* v_args_3952_, lean_object* v_body_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v_numParams_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; uint8_t v___x_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; 
v_numParams_3961_ = lean_ctor_get(v_v_3948_, 1);
lean_inc(v_numParams_3961_);
lean_dec(v_v_3948_);
lean_inc_ref(v_args_3952_);
v___x_3962_ = l_Array_toSubarray___redArg(v_args_3952_, v___x_3949_, v___x_3950_);
v___x_3963_ = l_Subarray_copy___redArg(v___x_3962_);
v___x_3964_ = lean_array_get_size(v_args_3952_);
v___x_3965_ = l_Array_toSubarray___redArg(v_args_3952_, v_numParams_3961_, v___x_3964_);
v___x_3966_ = l_Subarray_copy___redArg(v___x_3965_);
v___x_3967_ = l_Array_append___redArg(v___x_3963_, v___x_3966_);
lean_dec_ref(v___x_3966_);
v___x_3968_ = 0;
v___x_3969_ = 1;
v___x_3970_ = l_Lean_Meta_mkForallFVars(v___x_3967_, v_body_3953_, v___x_3968_, v___x_3951_, v___x_3951_, v___x_3969_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec_ref(v___x_3967_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v_v_3971_, lean_object* v___x_3972_, lean_object* v___x_3973_, lean_object* v___x_3974_, lean_object* v_args_3975_, lean_object* v_body_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
uint8_t v___x_5473__boxed_3984_; lean_object* v_res_3985_; 
v___x_5473__boxed_3984_ = lean_unbox(v___x_3974_);
v_res_3985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_3971_, v___x_3972_, v___x_3973_, v___x_5473__boxed_3984_, v_args_3975_, v_body_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_3986_, size_t v_sz_3987_, size_t v_i_3988_, lean_object* v_bs_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
uint8_t v___x_3997_; 
v___x_3997_ = lean_usize_dec_lt(v_i_3988_, v_sz_3987_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; 
lean_dec(v___x_3986_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v_bs_3989_);
return v___x_3998_;
}
else
{
lean_object* v_v_3999_; lean_object* v_toConstantVal_4000_; lean_object* v_name_4001_; lean_object* v_type_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___f_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; 
v_v_3999_ = lean_array_uget_borrowed(v_bs_3989_, v_i_3988_);
v_toConstantVal_4000_ = lean_ctor_get(v_v_3999_, 0);
v_name_4001_ = lean_ctor_get(v_toConstantVal_4000_, 0);
lean_inc(v_name_4001_);
v_type_4002_ = lean_ctor_get(v_toConstantVal_4000_, 2);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = lean_box(v___x_3997_);
lean_inc(v___x_3986_);
lean_inc(v_v_3999_);
v___f_4005_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4005_, 0, v_v_3999_);
lean_closure_set(v___f_4005_, 1, v___x_4003_);
lean_closure_set(v___f_4005_, 2, v___x_3986_);
lean_closure_set(v___f_4005_, 3, v___x_4004_);
v___x_4006_ = 0;
lean_inc_ref(v_type_4002_);
v___x_4007_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4002_, v___f_4005_, v___x_4006_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v_bs_x27_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; size_t v___x_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref(v___x_4007_);
v_bs_x27_4009_ = lean_array_uset(v_bs_3989_, v_i_3988_, v___x_4003_);
v___x_4010_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4001_);
v___x_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
lean_ctor_set(v___x_4011_, 1, v_a_4008_);
v___x_4012_ = ((size_t)1ULL);
v___x_4013_ = lean_usize_add(v_i_3988_, v___x_4012_);
v___x_4014_ = lean_array_uset(v_bs_x27_4009_, v_i_3988_, v___x_4011_);
v_i_3988_ = v___x_4013_;
v_bs_3989_ = v___x_4014_;
goto _start;
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_name_4001_);
lean_dec_ref(v_bs_3989_);
lean_dec(v___x_3986_);
v_a_4016_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4007_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4007_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___boxed(lean_object* v___x_4024_, lean_object* v_sz_4025_, lean_object* v_i_4026_, lean_object* v_bs_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
size_t v_sz_boxed_4035_; size_t v_i_boxed_4036_; lean_object* v_res_4037_; 
v_sz_boxed_4035_ = lean_unbox_usize(v_sz_4025_);
lean_dec(v_sz_4025_);
v_i_boxed_4036_ = lean_unbox_usize(v_i_4026_);
lean_dec(v_i_4026_);
v_res_4037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4024_, v_sz_boxed_4035_, v_i_boxed_4036_, v_bs_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(lean_object* v___x_4038_, size_t v_sz_4039_, size_t v_i_4040_, lean_object* v_bs_4041_){
_start:
{
uint8_t v___x_4042_; 
v___x_4042_ = lean_usize_dec_lt(v_i_4040_, v_sz_4039_);
if (v___x_4042_ == 0)
{
lean_dec(v___x_4038_);
return v_bs_4041_;
}
else
{
lean_object* v_v_4043_; lean_object* v_fst_4044_; lean_object* v___x_4045_; lean_object* v_bs_x27_4046_; lean_object* v___x_4047_; size_t v___x_4048_; size_t v___x_4049_; lean_object* v___x_4050_; 
v_v_4043_ = lean_array_uget_borrowed(v_bs_4041_, v_i_4040_);
v_fst_4044_ = lean_ctor_get(v_v_4043_, 0);
lean_inc(v_fst_4044_);
v___x_4045_ = lean_unsigned_to_nat(0u);
v_bs_x27_4046_ = lean_array_uset(v_bs_4041_, v_i_4040_, v___x_4045_);
lean_inc(v___x_4038_);
v___x_4047_ = l_Lean_mkConst(v_fst_4044_, v___x_4038_);
v___x_4048_ = ((size_t)1ULL);
v___x_4049_ = lean_usize_add(v_i_4040_, v___x_4048_);
v___x_4050_ = lean_array_uset(v_bs_x27_4046_, v_i_4040_, v___x_4047_);
v_i_4040_ = v___x_4049_;
v_bs_4041_ = v___x_4050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3___boxed(lean_object* v___x_4052_, lean_object* v_sz_4053_, lean_object* v_i_4054_, lean_object* v_bs_4055_){
_start:
{
size_t v_sz_boxed_4056_; size_t v_i_boxed_4057_; lean_object* v_res_4058_; 
v_sz_boxed_4056_ = lean_unbox_usize(v_sz_4053_);
lean_dec(v_sz_4053_);
v_i_boxed_4057_ = lean_unbox_usize(v_i_4054_);
lean_dec(v_i_4054_);
v_res_4058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4052_, v_sz_boxed_4056_, v_i_boxed_4057_, v_bs_4055_);
return v_res_4058_;
}
}
static lean_object* _init_l_Lean_Elab_Command_elabCoinductive___closed__1(void){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = ((lean_object*)(l_Lean_Elab_Command_elabCoinductive___closed__0));
v___x_4061_ = l_Lean_stringToMessageData(v___x_4060_);
return v___x_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive(lean_object* v_coinductiveElabData_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_){
_start:
{
lean_object* v_options_4070_; lean_object* v_inheritedTraceOptions_4071_; uint8_t v_hasTrace_4072_; lean_object* v___x_4073_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; 
v_options_4070_ = lean_ctor_get(v_a_4067_, 2);
v_inheritedTraceOptions_4071_ = lean_ctor_get(v_a_4067_, 13);
v_hasTrace_4072_ = lean_ctor_get_uint8(v_options_4070_, sizeof(void*)*1);
v___x_4073_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4072_ == 0)
{
v___y_4075_ = v_a_4063_;
v___y_4076_ = v_a_4064_;
v___y_4077_ = v_a_4065_;
v___y_4078_ = v_a_4066_;
v___y_4079_ = v_a_4067_;
v___y_4080_ = v_a_4068_;
goto v___jp_4074_;
}
else
{
lean_object* v_cls_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; 
v_cls_4141_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4143_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4070_, v___x_4142_);
if (v___x_4143_ == 0)
{
v___y_4075_ = v_a_4063_;
v___y_4076_ = v_a_4064_;
v___y_4077_ = v_a_4065_;
v___y_4078_ = v_a_4066_;
v___y_4079_ = v_a_4067_;
v___y_4080_ = v_a_4068_;
goto v___jp_4074_;
}
else
{
lean_object* v___x_4144_; size_t v_sz_4145_; size_t v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
v___x_4144_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4145_ = lean_array_size(v_coinductiveElabData_4062_);
v___x_4146_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4062_);
v___x_4147_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4145_, v___x_4146_, v_coinductiveElabData_4062_);
v___x_4148_ = lean_array_to_list(v___x_4147_);
v___x_4149_ = lean_box(0);
v___x_4150_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4148_, v___x_4149_);
v___x_4151_ = l_Lean_MessageData_ofList(v___x_4150_);
v___x_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4144_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4141_, v___x_4152_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_dec_ref(v___x_4153_);
v___y_4075_ = v_a_4063_;
v___y_4076_ = v_a_4064_;
v___y_4077_ = v_a_4065_;
v___y_4078_ = v_a_4066_;
v___y_4079_ = v_a_4067_;
v___y_4080_ = v_a_4068_;
goto v___jp_4074_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4062_);
return v___x_4153_;
}
}
}
v___jp_4074_:
{
size_t v_sz_4081_; size_t v___x_4082_; lean_object* v___x_4083_; 
v_sz_4081_ = lean_array_size(v_coinductiveElabData_4062_);
v___x_4082_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4062_);
v___x_4083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4081_, v___x_4082_, v_coinductiveElabData_4062_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v_toConstantVal_4087_; lean_object* v_numParams_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; size_t v_sz_4091_; lean_object* v___x_4092_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc_n(v_a_4084_, 2);
lean_dec_ref(v___x_4083_);
v___x_4085_ = lean_unsigned_to_nat(0u);
v___x_4086_ = lean_array_get_borrowed(v___x_4073_, v_a_4084_, v___x_4085_);
v_toConstantVal_4087_ = lean_ctor_get(v___x_4086_, 0);
v_numParams_4088_ = lean_ctor_get(v___x_4086_, 1);
v___x_4089_ = lean_array_get_size(v_a_4084_);
v___x_4090_ = lean_nat_sub(v_numParams_4088_, v___x_4089_);
v_sz_4091_ = lean_array_size(v_a_4084_);
lean_inc(v___x_4090_);
v___x_4092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4090_, v_sz_4091_, v___x_4082_, v_a_4084_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; lean_object* v_levelParams_4094_; lean_object* v_type_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; size_t v_sz_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___f_4102_; lean_object* v___x_4103_; uint8_t v___x_4104_; lean_object* v___x_4105_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc_n(v_a_4093_, 2);
lean_dec_ref(v___x_4092_);
v_levelParams_4094_ = lean_ctor_get(v_toConstantVal_4087_, 1);
v_type_4095_ = lean_ctor_get(v_toConstantVal_4087_, 2);
v___x_4096_ = lean_box(0);
lean_inc(v_levelParams_4094_);
v___x_4097_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4094_, v___x_4096_);
v_sz_4098_ = lean_array_size(v_a_4093_);
lean_inc(v___x_4097_);
v___x_4099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4097_, v_sz_4098_, v___x_4082_, v_a_4093_);
v___x_4100_ = lean_box_usize(v_sz_4091_);
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4084_);
v___f_4102_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4102_, 0, v___x_4097_);
lean_closure_set(v___f_4102_, 1, v___x_4099_);
lean_closure_set(v___f_4102_, 2, v___x_4100_);
lean_closure_set(v___f_4102_, 3, v___x_4101_);
lean_closure_set(v___f_4102_, 4, v_a_4084_);
lean_inc(v___x_4090_);
v___x_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4090_);
v___x_4104_ = 0;
lean_inc_ref(v_type_4095_);
v___x_4105_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4095_, v___x_4103_, v___f_4102_, v___x_4104_, v___x_4104_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v_lctx_4107_; lean_object* v_localInstances_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref(v___x_4105_);
v_lctx_4107_ = lean_ctor_get(v___y_4077_, 2);
v_localInstances_4108_ = lean_ctor_get(v___y_4077_, 3);
v___x_4109_ = lean_array_get_size(v_a_4106_);
v___x_4110_ = lean_mk_empty_array_with_capacity(v___x_4109_);
lean_inc(v_levelParams_4094_);
v___x_4111_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4062_, v_a_4093_, v_levelParams_4094_, v_a_4106_, v___x_4109_, v___x_4085_, v___x_4110_);
lean_dec(v_a_4106_);
lean_dec(v_a_4093_);
lean_inc_ref(v_localInstances_4108_);
lean_inc_ref(v_lctx_4107_);
v___x_4112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4112_, 0, v_lctx_4107_);
lean_ctor_set(v___x_4112_, 1, v_localInstances_4108_);
v___x_4113_ = l_Lean_Elab_partialFixpoint(v___x_4112_, v___x_4111_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v___x_4114_; 
lean_dec_ref(v___x_4113_);
lean_inc(v_a_4084_);
v___x_4114_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4084_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v___x_4115_; 
lean_dec_ref(v___x_4114_);
lean_inc(v_a_4084_);
v___x_4115_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4090_, v_a_4084_, v_coinductiveElabData_4062_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v___x_4116_; 
lean_dec_ref(v___x_4115_);
v___x_4116_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4084_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
return v___x_4116_;
}
else
{
lean_dec(v_a_4084_);
return v___x_4115_;
}
}
else
{
lean_dec(v___x_4090_);
lean_dec(v_a_4084_);
lean_dec_ref(v_coinductiveElabData_4062_);
return v___x_4114_;
}
}
else
{
lean_dec(v___x_4090_);
lean_dec(v_a_4084_);
lean_dec_ref(v_coinductiveElabData_4062_);
return v___x_4113_;
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec(v_a_4093_);
lean_dec(v___x_4090_);
lean_dec(v_a_4084_);
lean_dec_ref(v_coinductiveElabData_4062_);
v_a_4117_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4105_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4105_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
else
{
lean_object* v_a_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4132_; 
lean_dec(v___x_4090_);
lean_dec(v_a_4084_);
lean_dec_ref(v_coinductiveElabData_4062_);
v_a_4125_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4132_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4132_ == 0)
{
v___x_4127_ = v___x_4092_;
v_isShared_4128_ = v_isSharedCheck_4132_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_a_4125_);
lean_dec(v___x_4092_);
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
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec_ref(v_coinductiveElabData_4062_);
v_a_4133_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4083_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4083_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_){
_start:
{
lean_object* v_res_4162_; 
v_res_4162_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_, v_a_4160_);
lean_dec(v_a_4160_);
lean_dec_ref(v_a_4159_);
lean_dec(v_a_4158_);
lean_dec_ref(v_a_4157_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
return v_res_4162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4163_, lean_object* v___x_4164_, lean_object* v_params_4165_, size_t v_sz_4166_, size_t v_i_4167_, lean_object* v_bs_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4163_, v___x_4164_, v_params_4165_, v_sz_4166_, v_i_4167_, v_bs_4168_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4177_, lean_object* v___x_4178_, lean_object* v_params_4179_, lean_object* v_sz_4180_, lean_object* v_i_4181_, lean_object* v_bs_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
size_t v_sz_boxed_4190_; size_t v_i_boxed_4191_; lean_object* v_res_4192_; 
v_sz_boxed_4190_ = lean_unbox_usize(v_sz_4180_);
lean_dec(v_sz_4180_);
v_i_boxed_4191_ = lean_unbox_usize(v_i_4181_);
lean_dec(v_i_4181_);
v_res_4192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4177_, v___x_4178_, v_params_4179_, v_sz_boxed_4190_, v_i_boxed_4191_, v_bs_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4193_, lean_object* v_a_4194_, lean_object* v___x_4195_, lean_object* v_as_4196_, lean_object* v_i_4197_, lean_object* v_j_4198_, lean_object* v_inv_4199_, lean_object* v_bs_4200_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4193_, v_a_4194_, v___x_4195_, v_as_4196_, v_i_4197_, v_j_4198_, v_bs_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4202_, lean_object* v_a_4203_, lean_object* v___x_4204_, lean_object* v_as_4205_, lean_object* v_i_4206_, lean_object* v_j_4207_, lean_object* v_inv_4208_, lean_object* v_bs_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4202_, v_a_4203_, v___x_4204_, v_as_4205_, v_i_4206_, v_j_4207_, v_inv_4208_, v_bs_4209_);
lean_dec_ref(v_as_4205_);
lean_dec_ref(v_a_4203_);
lean_dec_ref(v_coinductiveElabData_4202_);
return v_res_4210_;
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
