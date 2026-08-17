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
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t, uint8_t);
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
v___x_191_ = lean_st_ref_put(v___y_172_, v___x_190_);
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
size_t v_x_8771__boxed_502_; size_t v_x_8772__boxed_503_; lean_object* v_res_504_; 
v_x_8771__boxed_502_ = lean_unbox_usize(v_x_498_);
lean_dec(v_x_498_);
v_x_8772__boxed_503_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_res_504_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_497_, v_x_8771__boxed_502_, v_x_8772__boxed_503_, v_x_500_, v_x_501_);
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
lean_object* v___x_516_; lean_object* v_mctx_517_; lean_object* v_cache_518_; lean_object* v_zetaDeltaFVarIds_519_; lean_object* v_postponed_520_; lean_object* v_diag_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_550_; 
v___x_516_ = lean_st_ref_take(v___y_514_);
v_mctx_517_ = lean_ctor_get(v___x_516_, 0);
v_cache_518_ = lean_ctor_get(v___x_516_, 1);
v_zetaDeltaFVarIds_519_ = lean_ctor_get(v___x_516_, 2);
v_postponed_520_ = lean_ctor_get(v___x_516_, 3);
v_diag_521_ = lean_ctor_get(v___x_516_, 4);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_516_);
if (v_isSharedCheck_550_ == 0)
{
v___x_523_ = v___x_516_;
v_isShared_524_ = v_isSharedCheck_550_;
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
v_isShared_524_ = v_isSharedCheck_550_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_depth_525_; lean_object* v_levelAssignDepth_526_; lean_object* v_lmvarCounter_527_; lean_object* v_mvarCounter_528_; lean_object* v_lDecls_529_; lean_object* v_decls_530_; lean_object* v_userNames_531_; lean_object* v_lAssignment_532_; lean_object* v_eAssignment_533_; lean_object* v_dAssignment_534_; lean_object* v_instanceTypedMVars_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_549_; 
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
v_instanceTypedMVars_535_ = lean_ctor_get(v_mctx_517_, 10);
v_isSharedCheck_549_ = !lean_is_exclusive(v_mctx_517_);
if (v_isSharedCheck_549_ == 0)
{
v___x_537_ = v_mctx_517_;
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_instanceTypedMVars_535_);
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
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_533_, v_mvarId_512_, v_val_513_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 8, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_depth_525_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_levelAssignDepth_526_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_lmvarCounter_527_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_mvarCounter_528_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_lDecls_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v_decls_530_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_userNames_531_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_lAssignment_532_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_548_, 9, v_dAssignment_534_);
lean_ctor_set(v_reuseFailAlloc_548_, 10, v_instanceTypedMVars_535_);
v___x_541_ = v_reuseFailAlloc_548_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 0, v___x_541_);
v___x_543_ = v___x_523_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_cache_518_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_zetaDeltaFVarIds_519_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_postponed_520_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_diag_521_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_st_ref_put(v___y_514_, v___x_543_);
v___x_545_ = lean_box(0);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
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
lean_object* v___x_562_; lean_object* v_env_563_; lean_object* v___x_564_; lean_object* v_mctx_565_; lean_object* v_lctx_566_; lean_object* v_options_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_562_ = lean_st_ref_get(v___y_560_);
v_env_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_ref(v_env_563_);
lean_dec(v___x_562_);
v___x_564_ = lean_st_ref_get(v___y_558_);
v_mctx_565_ = lean_ctor_get(v___x_564_, 0);
lean_inc_ref(v_mctx_565_);
lean_dec(v___x_564_);
v_lctx_566_ = lean_ctor_get(v___y_557_, 2);
v_options_567_ = lean_ctor_get(v___y_559_, 2);
lean_inc_ref(v_options_567_);
lean_inc_ref(v_lctx_566_);
v___x_568_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_568_, 0, v_env_563_);
lean_ctor_set(v___x_568_, 1, v_mctx_565_);
lean_ctor_set(v___x_568_, 2, v_lctx_566_);
lean_ctor_set(v___x_568_, 3, v_options_567_);
v___x_569_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
lean_ctor_set(v___x_569_, 1, v_msgData_556_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1___boxed(lean_object* v_msgData_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msgData_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(lean_object* v_msg_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_ref_584_; lean_object* v___x_585_; lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_594_; 
v_ref_584_ = lean_ctor_get(v___y_581_, 5);
v___x_585_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
v_a_586_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_594_ == 0)
{
v___x_588_ = v___x_585_;
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_594_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_inc(v_ref_584_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v_ref_584_);
lean_ctor_set(v___x_590_, 1, v_a_586_);
if (v_isShared_589_ == 0)
{
lean_ctor_set_tag(v___x_588_, 1);
lean_ctor_set(v___x_588_, 0, v___x_590_);
v___x_592_ = v___x_588_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg___boxed(lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_array_609_; lean_object* v_start_610_; lean_object* v_stop_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_626_; 
v_array_609_ = lean_ctor_get(v_a_602_, 0);
v_start_610_ = lean_ctor_get(v_a_602_, 1);
v_stop_611_ = lean_ctor_get(v_a_602_, 2);
v_isSharedCheck_626_ = !lean_is_exclusive(v_a_602_);
if (v_isSharedCheck_626_ == 0)
{
v___x_613_ = v_a_602_;
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_stop_611_);
lean_inc(v_start_610_);
lean_inc(v_array_609_);
lean_dec(v_a_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_626_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_lt(v_start_610_, v_stop_611_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; 
lean_del_object(v___x_613_);
lean_dec(v_stop_611_);
lean_dec(v_start_610_);
lean_dec_ref(v_array_609_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v_b_603_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_array_fget_borrowed(v_array_609_, v_start_610_);
lean_inc(v___x_617_);
v___x_618_ = l_Lean_Meta_mkCongrFun(v_b_603_, v___x_617_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = lean_nat_add(v_start_610_, v___x_620_);
lean_dec(v_start_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_621_);
v___x_623_ = v___x_613_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_array_609_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v_stop_611_);
v___x_623_ = v_reuseFailAlloc_625_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
v_a_602_ = v___x_623_;
v_b_603_ = v_a_619_;
goto _start;
}
}
else
{
lean_del_object(v___x_613_);
lean_dec(v_stop_611_);
lean_dec(v_start_610_);
lean_dec_ref(v_array_609_);
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg___boxed(lean_object* v_a_627_, lean_object* v_b_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_627_, v_b_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(lean_object* v_levels_635_, lean_object* v___x_636_, size_t v_sz_637_, size_t v_i_638_, lean_object* v_bs_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_638_, v_sz_637_);
if (v___x_640_ == 0)
{
lean_dec(v_levels_635_);
return v_bs_639_;
}
else
{
lean_object* v_v_641_; lean_object* v_toConstantVal_642_; lean_object* v_name_643_; lean_object* v___x_644_; lean_object* v_bs_x27_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v_v_641_ = lean_array_uget_borrowed(v_bs_639_, v_i_638_);
v_toConstantVal_642_ = lean_ctor_get(v_v_641_, 0);
v_name_643_ = lean_ctor_get(v_toConstantVal_642_, 0);
lean_inc(v_name_643_);
v___x_644_ = lean_unsigned_to_nat(0u);
v_bs_x27_645_ = lean_array_uset(v_bs_639_, v_i_638_, v___x_644_);
v___x_646_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_643_);
lean_inc(v_levels_635_);
v___x_647_ = l_Lean_mkConst(v___x_646_, v_levels_635_);
v___x_648_ = l_Lean_mkAppN(v___x_647_, v___x_636_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_add(v_i_638_, v___x_649_);
v___x_651_ = lean_array_uset(v_bs_x27_645_, v_i_638_, v___x_648_);
v_i_638_ = v___x_650_;
v_bs_639_ = v___x_651_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2___boxed(lean_object* v_levels_653_, lean_object* v___x_654_, lean_object* v_sz_655_, lean_object* v_i_656_, lean_object* v_bs_657_){
_start:
{
size_t v_sz_boxed_658_; size_t v_i_boxed_659_; lean_object* v_res_660_; 
v_sz_boxed_658_ = lean_unbox_usize(v_sz_655_);
lean_dec(v_sz_655_);
v_i_boxed_659_ = lean_unbox_usize(v_i_656_);
lean_dec(v_i_656_);
v_res_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_653_, v___x_654_, v_sz_boxed_658_, v_i_boxed_659_, v_bs_657_);
lean_dec_ref(v___x_654_);
return v_res_660_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__0));
v___x_663_ = l_Lean_stringToMessageData(v___x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(lean_object* v_infos_667_, lean_object* v_numParams_668_, lean_object* v___x_669_, lean_object* v_name_670_, lean_object* v_levels_671_, lean_object* v_args_672_, lean_object* v_x_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; size_t v_sz_690_; size_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_679_ = lean_array_get_size(v_infos_667_);
v___x_680_ = lean_nat_sub(v_numParams_668_, v___x_679_);
lean_inc(v___x_669_);
lean_inc_ref(v_args_672_);
v___x_681_ = l_Array_toSubarray___redArg(v_args_672_, v___x_669_, v___x_680_);
v___x_682_ = lean_array_get_size(v_args_672_);
v___x_683_ = l_Array_toSubarray___redArg(v_args_672_, v_numParams_668_, v___x_682_);
lean_inc_n(v_name_670_, 2);
v___x_684_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_670_);
lean_inc_n(v_levels_671_, 3);
lean_inc(v___x_684_);
v___x_685_ = l_Lean_mkConst(v___x_684_, v_levels_671_);
v___x_686_ = l_Subarray_copy___redArg(v___x_681_);
v___x_687_ = l_Lean_mkAppN(v___x_685_, v___x_686_);
lean_inc_ref(v___x_683_);
v___x_688_ = l_Subarray_copy___redArg(v___x_683_);
v___x_689_ = l_Lean_mkAppN(v___x_687_, v___x_688_);
v_sz_690_ = lean_array_size(v_infos_667_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__2(v_levels_671_, v___x_686_, v_sz_690_, v___x_691_, v_infos_667_);
v___x_693_ = l_Lean_mkConst(v_name_670_, v_levels_671_);
lean_inc_ref(v___x_686_);
v___x_694_ = l_Array_append___redArg(v___x_686_, v___x_692_);
lean_dec_ref(v___x_692_);
v___x_695_ = l_Array_append___redArg(v___x_694_, v___x_688_);
v___x_696_ = l_Lean_mkAppN(v___x_693_, v___x_695_);
lean_dec_ref(v___x_695_);
v___x_697_ = l_Lean_Meta_mkEq(v___x_689_, v___x_696_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_764_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_764_ == 0)
{
v___x_700_ = v___x_697_;
v_isShared_701_ = v_isSharedCheck_764_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_697_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_764_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 1);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_763_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
uint8_t v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = 0;
v___x_705_ = lean_box(0);
v___x_706_ = l_Lean_Meta_mkFreshExprMVar(v___x_703_, v___x_704_, v___x_705_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_Meta_getEqnsFor_x3f(v___x_684_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
if (lean_obj_tag(v_a_709_) == 1)
{
lean_object* v_val_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_val_717_ = lean_ctor_get(v_a_709_, 0);
lean_inc(v_val_717_);
lean_dec_ref_known(v_a_709_, 1);
v___x_718_ = lean_array_get_size(v_val_717_);
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_dec_eq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_dec(v_val_717_);
lean_dec(v_a_707_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec_ref(v___x_683_);
lean_dec(v_levels_671_);
lean_dec(v_name_670_);
lean_dec(v___x_669_);
v___y_711_ = v___y_674_;
v___y_712_ = v___y_675_;
v___y_713_ = v___y_676_;
v___y_714_ = v___y_677_;
goto v___jp_710_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_721_ = lean_array_fget(v_val_717_, v___x_669_);
lean_dec(v___x_669_);
lean_dec(v_val_717_);
v___x_722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__3));
v___x_723_ = l_Lean_Name_append(v_name_670_, v___x_722_);
lean_inc(v_levels_671_);
v___x_724_ = l_Lean_mkConst(v___x_723_, v_levels_671_);
v___x_725_ = l_Lean_mkConst(v___x_721_, v_levels_671_);
v___x_726_ = l_Lean_mkAppN(v___x_725_, v___x_686_);
v___x_727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v___x_683_, v___x_726_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
v___x_729_ = l_Lean_Expr_mvarId_x21(v_a_707_);
v___x_730_ = 0;
v___x_731_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_729_, v___x_724_, v___x_730_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_732_, v_a_728_, v___y_675_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; 
lean_dec_ref_known(v___x_733_, 1);
v___x_734_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_707_, v___y_675_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; uint8_t v___x_737_; lean_object* v___x_738_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
v___x_736_ = l_Array_append___redArg(v___x_686_, v___x_688_);
lean_dec_ref(v___x_688_);
v___x_737_ = 1;
v___x_738_ = l_Lean_Meta_mkLambdaFVars(v___x_736_, v_a_735_, v___x_730_, v___x_720_, v___x_730_, v___x_720_, v___x_737_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec_ref(v___x_736_);
return v___x_738_;
}
else
{
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
return v___x_734_;
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_a_707_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
v_a_739_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_733_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_733_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_a_728_);
lean_dec(v_a_707_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
v_a_747_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_731_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_731_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_dec_ref(v___x_724_);
lean_dec(v_a_707_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
return v___x_727_;
}
}
}
else
{
lean_dec(v_a_709_);
lean_dec(v_a_707_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec_ref(v___x_683_);
lean_dec(v_levels_671_);
lean_dec(v_name_670_);
lean_dec(v___x_669_);
v___y_711_ = v___y_674_;
v___y_712_ = v___y_675_;
v___y_713_ = v___y_676_;
v___y_714_ = v___y_677_;
goto v___jp_710_;
}
v___jp_710_:
{
lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_715_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___closed__1);
v___x_716_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_715_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
return v___x_716_;
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_707_);
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec_ref(v___x_683_);
lean_dec(v_levels_671_);
lean_dec(v_name_670_);
lean_dec(v___x_669_);
v_a_755_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_708_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_708_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v_levels_671_);
lean_dec(v_name_670_);
lean_dec(v___x_669_);
return v___x_706_;
}
}
}
}
else
{
lean_dec_ref(v___x_688_);
lean_dec_ref(v___x_686_);
lean_dec(v___x_684_);
lean_dec_ref(v___x_683_);
lean_dec(v_levels_671_);
lean_dec(v_name_670_);
lean_dec(v___x_669_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed(lean_object* v_infos_765_, lean_object* v_numParams_766_, lean_object* v___x_767_, lean_object* v_name_768_, lean_object* v_levels_769_, lean_object* v_args_770_, lean_object* v_x_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0(v_infos_765_, v_numParams_766_, v___x_767_, v_name_768_, v_levels_769_, v_args_770_, v_x_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec_ref(v_x_771_);
return v_res_777_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0(void){
_start:
{
lean_object* v___x_778_; double v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_float_of_nat(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(lean_object* v_cls_783_, lean_object* v_msg_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_ref_790_; lean_object* v___x_791_; lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_836_; 
v_ref_790_ = lean_ctor_get(v___y_787_, 5);
v___x_791_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_836_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_836_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_836_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_796_; lean_object* v_traceState_797_; lean_object* v_env_798_; lean_object* v_nextMacroScope_799_; lean_object* v_ngen_800_; lean_object* v_auxDeclNGen_801_; lean_object* v_cache_802_; lean_object* v_messages_803_; lean_object* v_infoState_804_; lean_object* v_snapshotTasks_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_835_; 
v___x_796_ = lean_st_ref_take(v___y_788_);
v_traceState_797_ = lean_ctor_get(v___x_796_, 4);
v_env_798_ = lean_ctor_get(v___x_796_, 0);
v_nextMacroScope_799_ = lean_ctor_get(v___x_796_, 1);
v_ngen_800_ = lean_ctor_get(v___x_796_, 2);
v_auxDeclNGen_801_ = lean_ctor_get(v___x_796_, 3);
v_cache_802_ = lean_ctor_get(v___x_796_, 5);
v_messages_803_ = lean_ctor_get(v___x_796_, 6);
v_infoState_804_ = lean_ctor_get(v___x_796_, 7);
v_snapshotTasks_805_ = lean_ctor_get(v___x_796_, 8);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_835_ == 0)
{
v___x_807_ = v___x_796_;
v_isShared_808_ = v_isSharedCheck_835_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_snapshotTasks_805_);
lean_inc(v_infoState_804_);
lean_inc(v_messages_803_);
lean_inc(v_cache_802_);
lean_inc(v_traceState_797_);
lean_inc(v_auxDeclNGen_801_);
lean_inc(v_ngen_800_);
lean_inc(v_nextMacroScope_799_);
lean_inc(v_env_798_);
lean_dec(v___x_796_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_835_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint64_t v_tid_809_; lean_object* v_traces_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_834_; 
v_tid_809_ = lean_ctor_get_uint64(v_traceState_797_, sizeof(void*)*1);
v_traces_810_ = lean_ctor_get(v_traceState_797_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_traceState_797_);
if (v_isSharedCheck_834_ == 0)
{
v___x_812_ = v_traceState_797_;
v_isShared_813_ = v_isSharedCheck_834_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_traces_810_);
lean_dec(v_traceState_797_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_834_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; double v___x_815_; uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_814_ = lean_box(0);
v___x_815_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_816_ = 0;
v___x_817_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_818_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_818_, 0, v_cls_783_);
lean_ctor_set(v___x_818_, 1, v___x_814_);
lean_ctor_set(v___x_818_, 2, v___x_817_);
lean_ctor_set_float(v___x_818_, sizeof(void*)*3, v___x_815_);
lean_ctor_set_float(v___x_818_, sizeof(void*)*3 + 8, v___x_815_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*3 + 16, v___x_816_);
v___x_819_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_820_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v_a_792_);
lean_ctor_set(v___x_820_, 2, v___x_819_);
lean_inc(v_ref_790_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v_ref_790_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Lean_PersistentArray_push___redArg(v_traces_810_, v___x_821_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_822_);
v___x_824_ = v___x_812_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_822_);
lean_ctor_set_uint64(v_reuseFailAlloc_833_, sizeof(void*)*1, v_tid_809_);
v___x_824_ = v_reuseFailAlloc_833_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_826_; 
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 4, v___x_824_);
v___x_826_ = v___x_807_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_env_798_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_nextMacroScope_799_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_ngen_800_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_auxDeclNGen_801_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v_cache_802_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_messages_803_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_infoState_804_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v_snapshotTasks_805_);
v___x_826_ = v_reuseFailAlloc_832_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_827_ = lean_st_ref_put(v___y_788_, v___x_826_);
v___x_828_ = lean_box(0);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v___x_828_);
v___x_830_ = v___x_794_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___boxed(lean_object* v_cls_837_, lean_object* v_msg_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v_cls_837_, v_msg_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
return v_res_844_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_853_ = l_Lean_Name_append(v___x_852_, v___x_851_);
return v___x_853_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__5));
v___x_856_ = l_Lean_stringToMessageData(v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(lean_object* v_infos_857_, lean_object* v_levels_858_, lean_object* v_as_859_, size_t v_sz_860_, size_t v_i_861_, lean_object* v_b_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
uint8_t v___x_868_; 
v___x_868_ = lean_usize_dec_lt(v_i_861_, v_sz_860_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_levels_858_);
lean_dec_ref(v_infos_857_);
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_b_862_);
return v___x_869_;
}
else
{
lean_object* v_a_870_; lean_object* v_toConstantVal_871_; lean_object* v_numParams_872_; lean_object* v_name_873_; lean_object* v_levelParams_874_; lean_object* v_type_875_; lean_object* v___x_876_; lean_object* v___f_877_; uint8_t v___x_878_; lean_object* v___x_879_; 
v_a_870_ = lean_array_uget_borrowed(v_as_859_, v_i_861_);
v_toConstantVal_871_ = lean_ctor_get(v_a_870_, 0);
v_numParams_872_ = lean_ctor_get(v_a_870_, 1);
v_name_873_ = lean_ctor_get(v_toConstantVal_871_, 0);
v_levelParams_874_ = lean_ctor_get(v_toConstantVal_871_, 1);
v_type_875_ = lean_ctor_get(v_toConstantVal_871_, 2);
v___x_876_ = lean_unsigned_to_nat(0u);
lean_inc(v_levels_858_);
lean_inc(v_name_873_);
lean_inc(v_numParams_872_);
lean_inc_ref(v_infos_857_);
v___f_877_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___lam__0___boxed), 12, 5);
lean_closure_set(v___f_877_, 0, v_infos_857_);
lean_closure_set(v___f_877_, 1, v_numParams_872_);
lean_closure_set(v___f_877_, 2, v___x_876_);
lean_closure_set(v___f_877_, 3, v_name_873_);
lean_closure_set(v___f_877_, 4, v_levels_858_);
v___x_878_ = 0;
lean_inc_ref(v_type_875_);
v___x_879_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg(v_type_875_, v___f_877_, v___x_878_, v___x_878_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_options_880_; lean_object* v_a_881_; lean_object* v_inheritedTraceOptions_882_; uint8_t v_hasTrace_883_; lean_object* v___x_884_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_889_; 
v_options_880_ = lean_ctor_get(v___y_865_, 2);
v_a_881_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_879_, 1);
v_inheritedTraceOptions_882_ = lean_ctor_get(v___y_865_, 13);
v_hasTrace_883_ = lean_ctor_get_uint8(v_options_880_, sizeof(void*)*1);
v___x_884_ = lean_box(0);
if (v_hasTrace_883_ == 0)
{
v___y_886_ = v___y_863_;
v___y_887_ = v___y_864_;
v___y_888_ = v___y_865_;
v___y_889_ = v___y_866_;
goto v___jp_885_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_919_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_921_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_882_, v_options_880_, v___x_920_);
if (v___x_921_ == 0)
{
v___y_886_ = v___y_863_;
v___y_887_ = v___y_864_;
v___y_888_ = v___y_865_;
v___y_889_ = v___y_866_;
goto v___jp_885_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_922_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__6);
lean_inc(v_a_881_);
v___x_923_ = l_Lean_MessageData_ofExpr(v_a_881_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8(v___x_919_, v___x_924_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_dec_ref_known(v___x_925_, 1);
v___y_886_ = v___y_863_;
v___y_887_ = v___y_864_;
v___y_888_ = v___y_865_;
v___y_889_ = v___y_866_;
goto v___jp_885_;
}
else
{
lean_dec(v_a_881_);
lean_dec(v_levels_858_);
lean_dec_ref(v_infos_857_);
return v___x_925_;
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
lean_inc(v_a_881_);
v___x_890_ = lean_infer_type(v_a_881_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
lean_inc(v_name_873_);
v___x_892_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_873_);
v___x_893_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_894_ = l_Lean_Name_append(v___x_892_, v___x_893_);
v___x_895_ = lean_box(0);
lean_inc(v_levelParams_874_);
v___x_896_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_894_, v_levelParams_874_, v_a_891_, v_a_881_, v___x_895_, v___y_889_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc(v_a_897_);
lean_dec_ref_known(v___x_896_, 1);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_a_897_);
v___x_899_ = l_Lean_addDecl(v___x_898_, v___x_878_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_899_) == 0)
{
size_t v___x_900_; size_t v___x_901_; 
lean_dec_ref_known(v___x_899_, 1);
v___x_900_ = ((size_t)1ULL);
v___x_901_ = lean_usize_add(v_i_861_, v___x_900_);
v_i_861_ = v___x_901_;
v_b_862_ = v___x_884_;
goto _start;
}
else
{
lean_dec(v_levels_858_);
lean_dec_ref(v_infos_857_);
return v___x_899_;
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec(v_levels_858_);
lean_dec_ref(v_infos_857_);
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
lean_dec(v_a_881_);
lean_dec(v_levels_858_);
lean_dec_ref(v_infos_857_);
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
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_levels_858_);
lean_dec_ref(v_infos_857_);
v_a_926_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_879_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_879_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___boxed(lean_object* v_infos_934_, lean_object* v_levels_935_, lean_object* v_as_936_, lean_object* v_sz_937_, lean_object* v_i_938_, lean_object* v_b_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
size_t v_sz_boxed_945_; size_t v_i_boxed_946_; lean_object* v_res_947_; 
v_sz_boxed_945_ = lean_unbox_usize(v_sz_937_);
lean_dec(v_sz_937_);
v_i_boxed_946_ = lean_unbox_usize(v_i_938_);
lean_dec(v_i_938_);
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_934_, v_levels_935_, v_as_936_, v_sz_boxed_945_, v_i_boxed_946_, v_b_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec_ref(v_as_936_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(lean_object* v_infos_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v_toConstantVal_957_; lean_object* v_levelParams_958_; lean_object* v___x_959_; lean_object* v_levels_960_; lean_object* v___x_961_; size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_954_ = l_Lean_instInhabitedInductiveVal_default;
v___x_955_ = lean_unsigned_to_nat(0u);
v___x_956_ = lean_array_get_borrowed(v___x_954_, v_infos_948_, v___x_955_);
v_toConstantVal_957_ = lean_ctor_get(v___x_956_, 0);
v_levelParams_958_ = lean_ctor_get(v_toConstantVal_957_, 1);
v___x_959_ = lean_box(0);
lean_inc(v_levelParams_958_);
v_levels_960_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_958_, v___x_959_);
v___x_961_ = lean_box(0);
v_sz_962_ = lean_array_size(v_infos_948_);
v___x_963_ = ((size_t)0ULL);
lean_inc_ref(v_infos_948_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9(v_infos_948_, v_levels_960_, v_infos_948_, v_sz_962_, v___x_963_, v___x_961_, v_a_949_, v_a_950_, v_a_951_, v_a_952_);
lean_dec_ref(v_infos_948_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_971_; 
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_971_ == 0)
{
lean_object* v_unused_972_; 
v_unused_972_ = lean_ctor_get(v___x_964_, 0);
lean_dec(v_unused_972_);
v___x_966_ = v___x_964_;
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
else
{
lean_dec(v___x_964_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_971_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v___x_969_; 
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_961_);
v___x_969_ = v___x_966_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_961_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
else
{
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas___boxed(lean_object* v_infos_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_infos_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(lean_object* v_00_u03b1_980_, lean_object* v_msg_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___boxed(lean_object* v_00_u03b1_988_, lean_object* v_msg_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1(v_00_u03b1_988_, v_msg_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(lean_object* v_inst_996_, lean_object* v_R_997_, lean_object* v_a_998_, lean_object* v_b_999_, lean_object* v_c_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___redArg(v_a_998_, v_b_999_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3___boxed(lean_object* v_inst_1007_, lean_object* v_R_1008_, lean_object* v_a_1009_, lean_object* v_b_1010_, lean_object* v_c_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__3(v_inst_1007_, v_R_1008_, v_a_1009_, v_b_1010_, v_c_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(lean_object* v_mvarId_1018_, lean_object* v_val_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_mvarId_1018_, v_val_1019_, v___y_1021_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___boxed(lean_object* v_mvarId_1026_, lean_object* v_val_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4(v_mvarId_1026_, v_val_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5(lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_x_1035_, v_x_1036_, v_x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(lean_object* v_00_u03b2_1039_, lean_object* v_x_1040_, size_t v_x_1041_, size_t v_x_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_1040_, v_x_1041_, v_x_1042_, v_x_1043_, v_x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
size_t v_x_9699__boxed_1052_; size_t v_x_9700__boxed_1053_; lean_object* v_res_1054_; 
v_x_9699__boxed_1052_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_x_9700__boxed_1053_ = lean_unbox_usize(v_x_1049_);
lean_dec(v_x_1049_);
v_res_1054_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9(v_00_u03b2_1046_, v_x_1047_, v_x_9699__boxed_1052_, v_x_9700__boxed_1053_, v_x_1050_, v_x_1051_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12(lean_object* v_00_u03b2_1055_, lean_object* v_n_1056_, lean_object* v_k_1057_, lean_object* v_v_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v_n_1056_, v_k_1057_, v_v_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(lean_object* v_00_u03b2_1060_, size_t v_depth_1061_, lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_heq_1064_, lean_object* v_i_1065_, lean_object* v_entries_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_1061_, v_keys_1062_, v_vals_1063_, v_i_1065_, v_entries_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___boxed(lean_object* v_00_u03b2_1068_, lean_object* v_depth_1069_, lean_object* v_keys_1070_, lean_object* v_vals_1071_, lean_object* v_heq_1072_, lean_object* v_i_1073_, lean_object* v_entries_1074_){
_start:
{
size_t v_depth_boxed_1075_; lean_object* v_res_1076_; 
v_depth_boxed_1075_ = lean_unbox_usize(v_depth_1069_);
lean_dec(v_depth_1069_);
v_res_1076_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13(v_00_u03b2_1068_, v_depth_boxed_1075_, v_keys_1070_, v_vals_1071_, v_heq_1072_, v_i_1073_, v_entries_1074_);
lean_dec_ref(v_vals_1071_);
lean_dec_ref(v_keys_1070_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12_spec__13___redArg(v_x_1078_, v_x_1079_, v_x_1080_, v_x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(lean_object* v_e_1083_, lean_object* v___y_1084_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Lean_Expr_hasMVar(v_e_1083_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v_e_1083_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; lean_object* v_mctx_1089_; lean_object* v___x_1090_; lean_object* v_fst_1091_; lean_object* v_snd_1092_; lean_object* v___x_1093_; lean_object* v_cache_1094_; lean_object* v_zetaDeltaFVarIds_1095_; lean_object* v_postponed_1096_; lean_object* v_diag_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1106_; 
v___x_1088_ = lean_st_ref_get(v___y_1084_);
v_mctx_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc_ref(v_mctx_1089_);
lean_dec(v___x_1088_);
v___x_1090_ = l_Lean_instantiateMVarsCore(v_mctx_1089_, v_e_1083_);
v_fst_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_fst_1091_);
v_snd_1092_ = lean_ctor_get(v___x_1090_, 1);
lean_inc(v_snd_1092_);
lean_dec_ref(v___x_1090_);
v___x_1093_ = lean_st_ref_take(v___y_1084_);
v_cache_1094_ = lean_ctor_get(v___x_1093_, 1);
v_zetaDeltaFVarIds_1095_ = lean_ctor_get(v___x_1093_, 2);
v_postponed_1096_ = lean_ctor_get(v___x_1093_, 3);
v_diag_1097_ = lean_ctor_get(v___x_1093_, 4);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1106_ == 0)
{
lean_object* v_unused_1107_; 
v_unused_1107_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1107_);
v___x_1099_ = v___x_1093_;
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_diag_1097_);
lean_inc(v_postponed_1096_);
lean_inc(v_zetaDeltaFVarIds_1095_);
lean_inc(v_cache_1094_);
lean_dec(v___x_1093_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1106_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
lean_ctor_set(v___x_1099_, 0, v_snd_1092_);
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_snd_1092_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_cache_1094_);
lean_ctor_set(v_reuseFailAlloc_1105_, 2, v_zetaDeltaFVarIds_1095_);
lean_ctor_set(v_reuseFailAlloc_1105_, 3, v_postponed_1096_);
lean_ctor_set(v_reuseFailAlloc_1105_, 4, v_diag_1097_);
v___x_1102_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_st_ref_put(v___y_1084_, v___x_1102_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_fst_1091_);
return v___x_1104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_e_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1108_, v___y_1109_);
lean_dec(v___y_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_e_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1112_, v___y_1116_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_e_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
lean_dec(v___y_1125_);
lean_dec_ref(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object* v_k_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v_b_1133_, lean_object* v_c_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_){
_start:
{
lean_object* v___x_1140_; 
lean_inc(v___y_1138_);
lean_inc_ref(v___y_1137_);
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
v___x_1140_ = lean_apply_9(v_k_1130_, v_b_1133_, v_c_1134_, v___y_1131_, v___y_1132_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, lean_box(0));
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object* v_k_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v_b_1144_, lean_object* v_c_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1141_, v___y_1142_, v___y_1143_, v_b_1144_, v_c_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_type_1152_, lean_object* v_k_1153_, uint8_t v_cleanupAnnotations_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___f_1162_; uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_inc(v___y_1156_);
lean_inc_ref(v___y_1155_);
v___f_1162_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1162_, 0, v_k_1153_);
lean_closure_set(v___f_1162_, 1, v___y_1155_);
lean_closure_set(v___f_1162_, 2, v___y_1156_);
v___x_1163_ = 0;
v___x_1164_ = lean_box(0);
v___x_1165_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1163_, v___x_1164_, v_type_1152_, v___f_1162_, v_cleanupAnnotations_1154_, v___x_1163_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
if (lean_obj_tag(v___x_1165_) == 0)
{
return v___x_1165_;
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1165_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_type_1174_, lean_object* v_k_1175_, lean_object* v_cleanupAnnotations_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1184_; lean_object* v_res_1185_; 
v_cleanupAnnotations_boxed_1184_ = lean_unbox(v_cleanupAnnotations_1176_);
v_res_1185_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1174_, v_k_1175_, v_cleanupAnnotations_boxed_1184_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_00_u03b1_1186_, lean_object* v_type_1187_, lean_object* v_k_1188_, uint8_t v_cleanupAnnotations_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1187_, v_k_1188_, v_cleanupAnnotations_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_00_u03b1_1198_, lean_object* v_type_1199_, lean_object* v_k_1200_, lean_object* v_cleanupAnnotations_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1209_; lean_object* v_res_1210_; 
v_cleanupAnnotations_boxed_1209_ = lean_unbox(v_cleanupAnnotations_1201_);
v_res_1210_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_1198_, v_type_1199_, v_k_1200_, v_cleanupAnnotations_boxed_1209_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_name_1211_, lean_object* v_levelParams_1212_, lean_object* v_type_1213_, lean_object* v_value_1214_, lean_object* v_hints_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v___x_1218_; uint8_t v___y_1220_; uint8_t v___y_1227_; lean_object* v_env_1230_; uint8_t v___x_1231_; 
v___x_1218_ = lean_st_ref_get(v___y_1216_);
v_env_1230_ = lean_ctor_get(v___x_1218_, 0);
lean_inc_ref_n(v_env_1230_, 2);
lean_dec(v___x_1218_);
v___x_1231_ = l_Lean_Environment_hasUnsafe(v_env_1230_, v_type_1213_);
if (v___x_1231_ == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = l_Lean_Environment_hasUnsafe(v_env_1230_, v_value_1214_);
v___y_1227_ = v___x_1232_;
goto v___jp_1226_;
}
else
{
lean_dec_ref(v_env_1230_);
v___y_1227_ = v___x_1231_;
goto v___jp_1226_;
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_inc(v_name_1211_);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v_name_1211_);
lean_ctor_set(v___x_1221_, 1, v_levelParams_1212_);
lean_ctor_set(v___x_1221_, 2, v_type_1213_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_name_1211_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1224_, 0, v___x_1221_);
lean_ctor_set(v___x_1224_, 1, v_value_1214_);
lean_ctor_set(v___x_1224_, 2, v_hints_1215_);
lean_ctor_set(v___x_1224_, 3, v___x_1223_);
lean_ctor_set_uint8(v___x_1224_, sizeof(void*)*4, v___y_1220_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
v___jp_1226_:
{
if (v___y_1227_ == 0)
{
uint8_t v___x_1228_; 
v___x_1228_ = 1;
v___y_1220_ = v___x_1228_;
goto v___jp_1219_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
v___y_1220_ = v___x_1229_;
goto v___jp_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1233_, lean_object* v_levelParams_1234_, lean_object* v_type_1235_, lean_object* v_value_1236_, lean_object* v_hints_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1233_, v_levelParams_1234_, v_type_1235_, v_value_1236_, v_hints_1237_, v___y_1238_);
lean_dec(v___y_1238_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1241_, lean_object* v_levelParams_1242_, lean_object* v_type_1243_, lean_object* v_value_1244_, lean_object* v_hints_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1241_, v_levelParams_1242_, v_type_1243_, v_value_1244_, v_hints_1245_, v___y_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1254_, lean_object* v_levelParams_1255_, lean_object* v_type_1256_, lean_object* v_value_1257_, lean_object* v_hints_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1254_, v_levelParams_1255_, v_type_1256_, v_value_1257_, v_hints_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1267_, lean_object* v_maxFVars_x3f_1268_, lean_object* v_k_1269_, uint8_t v_cleanupAnnotations_1270_, uint8_t v_whnfType_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
lean_object* v___f_1279_; lean_object* v___x_1280_; 
lean_inc(v___y_1273_);
lean_inc_ref(v___y_1272_);
v___f_1279_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1279_, 0, v_k_1269_);
lean_closure_set(v___f_1279_, 1, v___y_1272_);
lean_closure_set(v___f_1279_, 2, v___y_1273_);
v___x_1280_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1267_, v_maxFVars_x3f_1268_, v___f_1279_, v_cleanupAnnotations_1270_, v_whnfType_1271_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
if (lean_obj_tag(v___x_1280_) == 0)
{
return v___x_1280_;
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1289_, lean_object* v_maxFVars_x3f_1290_, lean_object* v_k_1291_, lean_object* v_cleanupAnnotations_1292_, lean_object* v_whnfType_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1301_; uint8_t v_whnfType_boxed_1302_; lean_object* v_res_1303_; 
v_cleanupAnnotations_boxed_1301_ = lean_unbox(v_cleanupAnnotations_1292_);
v_whnfType_boxed_1302_ = lean_unbox(v_whnfType_1293_);
v_res_1303_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1289_, v_maxFVars_x3f_1290_, v_k_1291_, v_cleanupAnnotations_boxed_1301_, v_whnfType_boxed_1302_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1304_, lean_object* v_type_1305_, lean_object* v_maxFVars_x3f_1306_, lean_object* v_k_1307_, uint8_t v_cleanupAnnotations_1308_, uint8_t v_whnfType_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1305_, v_maxFVars_x3f_1306_, v_k_1307_, v_cleanupAnnotations_1308_, v_whnfType_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1318_, lean_object* v_type_1319_, lean_object* v_maxFVars_x3f_1320_, lean_object* v_k_1321_, lean_object* v_cleanupAnnotations_1322_, lean_object* v_whnfType_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1331_; uint8_t v_whnfType_boxed_1332_; lean_object* v_res_1333_; 
v_cleanupAnnotations_boxed_1331_ = lean_unbox(v_cleanupAnnotations_1322_);
v_whnfType_boxed_1332_ = lean_unbox(v_whnfType_1323_);
v_res_1333_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1318_, v_type_1319_, v_maxFVars_x3f_1320_, v_k_1321_, v_cleanupAnnotations_boxed_1331_, v_whnfType_boxed_1332_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_options_1342_; uint8_t v_hasTrace_1343_; 
v_options_1342_ = lean_ctor_get(v___y_1339_, 2);
v_hasTrace_1343_ = lean_ctor_get_uint8(v_options_1342_, sizeof(void*)*1);
if (v_hasTrace_1343_ == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
lean_dec(v_cls_1334_);
v___x_1344_ = lean_box(v_hasTrace_1343_);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
return v___x_1345_;
}
else
{
lean_object* v_inheritedTraceOptions_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_inheritedTraceOptions_1346_ = lean_ctor_get(v___y_1339_, 13);
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1348_ = l_Lean_Name_append(v___x_1347_, v_cls_1334_);
v___x_1349_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1346_, v_options_1342_, v___x_1348_);
lean_dec(v___x_1348_);
v___x_1350_ = lean_box(v___x_1349_);
v___x_1351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object* v_cls_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_mvarId_1361_, lean_object* v_val_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; lean_object* v_mctx_1366_; lean_object* v_cache_1367_; lean_object* v_zetaDeltaFVarIds_1368_; lean_object* v_postponed_1369_; lean_object* v_diag_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1399_; 
v___x_1365_ = lean_st_ref_take(v___y_1363_);
v_mctx_1366_ = lean_ctor_get(v___x_1365_, 0);
v_cache_1367_ = lean_ctor_get(v___x_1365_, 1);
v_zetaDeltaFVarIds_1368_ = lean_ctor_get(v___x_1365_, 2);
v_postponed_1369_ = lean_ctor_get(v___x_1365_, 3);
v_diag_1370_ = lean_ctor_get(v___x_1365_, 4);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1372_ = v___x_1365_;
v_isShared_1373_ = v_isSharedCheck_1399_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_diag_1370_);
lean_inc(v_postponed_1369_);
lean_inc(v_zetaDeltaFVarIds_1368_);
lean_inc(v_cache_1367_);
lean_inc(v_mctx_1366_);
lean_dec(v___x_1365_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1399_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_depth_1374_; lean_object* v_levelAssignDepth_1375_; lean_object* v_lmvarCounter_1376_; lean_object* v_mvarCounter_1377_; lean_object* v_lDecls_1378_; lean_object* v_decls_1379_; lean_object* v_userNames_1380_; lean_object* v_lAssignment_1381_; lean_object* v_eAssignment_1382_; lean_object* v_dAssignment_1383_; lean_object* v_instanceTypedMVars_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1398_; 
v_depth_1374_ = lean_ctor_get(v_mctx_1366_, 0);
v_levelAssignDepth_1375_ = lean_ctor_get(v_mctx_1366_, 1);
v_lmvarCounter_1376_ = lean_ctor_get(v_mctx_1366_, 2);
v_mvarCounter_1377_ = lean_ctor_get(v_mctx_1366_, 3);
v_lDecls_1378_ = lean_ctor_get(v_mctx_1366_, 4);
v_decls_1379_ = lean_ctor_get(v_mctx_1366_, 5);
v_userNames_1380_ = lean_ctor_get(v_mctx_1366_, 6);
v_lAssignment_1381_ = lean_ctor_get(v_mctx_1366_, 7);
v_eAssignment_1382_ = lean_ctor_get(v_mctx_1366_, 8);
v_dAssignment_1383_ = lean_ctor_get(v_mctx_1366_, 9);
v_instanceTypedMVars_1384_ = lean_ctor_get(v_mctx_1366_, 10);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_mctx_1366_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1386_ = v_mctx_1366_;
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_instanceTypedMVars_1384_);
lean_inc(v_dAssignment_1383_);
lean_inc(v_eAssignment_1382_);
lean_inc(v_lAssignment_1381_);
lean_inc(v_userNames_1380_);
lean_inc(v_decls_1379_);
lean_inc(v_lDecls_1378_);
lean_inc(v_mvarCounter_1377_);
lean_inc(v_lmvarCounter_1376_);
lean_inc(v_levelAssignDepth_1375_);
lean_inc(v_depth_1374_);
lean_dec(v_mctx_1366_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1382_, v_mvarId_1361_, v_val_1362_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 8, v___x_1388_);
v___x_1390_ = v___x_1386_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_depth_1374_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_levelAssignDepth_1375_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_lmvarCounter_1376_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_mvarCounter_1377_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_lDecls_1378_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v_decls_1379_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_userNames_1380_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_lAssignment_1381_);
lean_ctor_set(v_reuseFailAlloc_1397_, 8, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1397_, 9, v_dAssignment_1383_);
lean_ctor_set(v_reuseFailAlloc_1397_, 10, v_instanceTypedMVars_1384_);
v___x_1390_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1390_);
v___x_1392_ = v___x_1372_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_cache_1367_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_zetaDeltaFVarIds_1368_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_postponed_1369_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_diag_1370_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_st_ref_put(v___y_1363_, v___x_1392_);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
return v___x_1395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg___boxed(lean_object* v_mvarId_1400_, lean_object* v_val_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1400_, v_val_1401_, v___y_1402_);
lean_dec(v___y_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(lean_object* v_cls_1405_, lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_ref_1412_; lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1458_; 
v_ref_1412_ = lean_ctor_get(v___y_1409_, 5);
v___x_1413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1458_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1458_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v_traceState_1419_; lean_object* v_env_1420_; lean_object* v_nextMacroScope_1421_; lean_object* v_ngen_1422_; lean_object* v_auxDeclNGen_1423_; lean_object* v_cache_1424_; lean_object* v_messages_1425_; lean_object* v_infoState_1426_; lean_object* v_snapshotTasks_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1457_; 
v___x_1418_ = lean_st_ref_take(v___y_1410_);
v_traceState_1419_ = lean_ctor_get(v___x_1418_, 4);
v_env_1420_ = lean_ctor_get(v___x_1418_, 0);
v_nextMacroScope_1421_ = lean_ctor_get(v___x_1418_, 1);
v_ngen_1422_ = lean_ctor_get(v___x_1418_, 2);
v_auxDeclNGen_1423_ = lean_ctor_get(v___x_1418_, 3);
v_cache_1424_ = lean_ctor_get(v___x_1418_, 5);
v_messages_1425_ = lean_ctor_get(v___x_1418_, 6);
v_infoState_1426_ = lean_ctor_get(v___x_1418_, 7);
v_snapshotTasks_1427_ = lean_ctor_get(v___x_1418_, 8);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1429_ = v___x_1418_;
v_isShared_1430_ = v_isSharedCheck_1457_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_snapshotTasks_1427_);
lean_inc(v_infoState_1426_);
lean_inc(v_messages_1425_);
lean_inc(v_cache_1424_);
lean_inc(v_traceState_1419_);
lean_inc(v_auxDeclNGen_1423_);
lean_inc(v_ngen_1422_);
lean_inc(v_nextMacroScope_1421_);
lean_inc(v_env_1420_);
lean_dec(v___x_1418_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1457_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
uint64_t v_tid_1431_; lean_object* v_traces_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1456_; 
v_tid_1431_ = lean_ctor_get_uint64(v_traceState_1419_, sizeof(void*)*1);
v_traces_1432_ = lean_ctor_get(v_traceState_1419_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_traceState_1419_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1434_ = v_traceState_1419_;
v_isShared_1435_ = v_isSharedCheck_1456_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_traces_1432_);
lean_dec(v_traceState_1419_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1456_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; double v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__0);
v___x_1438_ = 0;
v___x_1439_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__1));
v___x_1440_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1440_, 0, v_cls_1405_);
lean_ctor_set(v___x_1440_, 1, v___x_1436_);
lean_ctor_set(v___x_1440_, 2, v___x_1439_);
lean_ctor_set_float(v___x_1440_, sizeof(void*)*3, v___x_1437_);
lean_ctor_set_float(v___x_1440_, sizeof(void*)*3 + 8, v___x_1437_);
lean_ctor_set_uint8(v___x_1440_, sizeof(void*)*3 + 16, v___x_1438_);
v___x_1441_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__8___closed__2));
v___x_1442_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1440_);
lean_ctor_set(v___x_1442_, 1, v_a_1414_);
lean_ctor_set(v___x_1442_, 2, v___x_1441_);
lean_inc(v_ref_1412_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v_ref_1412_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_PersistentArray_push___redArg(v_traces_1432_, v___x_1443_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 0, v___x_1444_);
v___x_1446_ = v___x_1434_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1444_);
lean_ctor_set_uint64(v_reuseFailAlloc_1455_, sizeof(void*)*1, v_tid_1431_);
v___x_1446_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1448_; 
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 4, v___x_1446_);
v___x_1448_ = v___x_1429_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_env_1420_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_nextMacroScope_1421_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_ngen_1422_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_auxDeclNGen_1423_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1454_, 5, v_cache_1424_);
lean_ctor_set(v_reuseFailAlloc_1454_, 6, v_messages_1425_);
lean_ctor_set(v_reuseFailAlloc_1454_, 7, v_infoState_1426_);
lean_ctor_set(v_reuseFailAlloc_1454_, 8, v_snapshotTasks_1427_);
v___x_1448_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1449_ = lean_st_ref_put(v___y_1410_, v___x_1448_);
v___x_1450_ = lean_box(0);
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1450_);
v___x_1452_ = v___x_1416_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg___boxed(lean_object* v_cls_1459_, lean_object* v_msg_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1459_, v_msg_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1467_; lean_object* v_dummy_1468_; 
v___x_1467_ = lean_box(0);
v_dummy_1468_ = l_Lean_Expr_sort___override(v___x_1467_);
return v_dummy_1468_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__1));
v___x_1471_ = l_Lean_stringToMessageData(v___x_1470_);
return v___x_1471_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1473_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__3));
v___x_1474_ = l_Lean_stringToMessageData(v___x_1473_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(lean_object* v_numParams_1475_, lean_object* v___x_1476_, lean_object* v_name_1477_, lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v_name_1480_, lean_object* v___x_1481_, lean_object* v_cls_1482_, lean_object* v_fields_1483_, lean_object* v_bodyExpr_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_options_1492_; lean_object* v_inheritedTraceOptions_1493_; uint8_t v_hasTrace_1494_; lean_object* v_nargs_1495_; lean_object* v_dummy_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; 
v_options_1492_ = lean_ctor_get(v___y_1489_, 2);
v_inheritedTraceOptions_1493_ = lean_ctor_get(v___y_1489_, 13);
v_hasTrace_1494_ = lean_ctor_get_uint8(v_options_1492_, sizeof(void*)*1);
v_nargs_1495_ = l_Lean_Expr_getAppNumArgs(v_bodyExpr_1484_);
v_dummy_1496_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
lean_inc(v_nargs_1495_);
v___x_1497_ = lean_mk_array(v_nargs_1495_, v_dummy_1496_);
v___x_1498_ = lean_unsigned_to_nat(1u);
v___x_1499_ = lean_nat_sub(v_nargs_1495_, v___x_1498_);
lean_dec(v_nargs_1495_);
v___x_1500_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_bodyExpr_1484_, v___x_1497_, v___x_1499_);
v___x_1501_ = lean_array_get_size(v___x_1500_);
v___x_1502_ = lean_nat_add(v_numParams_1475_, v___x_1476_);
v___x_1503_ = l_Array_toSubarray___redArg(v___x_1500_, v___x_1502_, v___x_1501_);
v___x_1504_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1477_);
lean_inc(v___x_1478_);
lean_inc(v___x_1504_);
v___x_1505_ = l_Lean_mkConst(v___x_1504_, v___x_1478_);
v___x_1506_ = l_Lean_mkAppN(v___x_1505_, v___x_1479_);
v___x_1507_ = l_Subarray_copy___redArg(v___x_1503_);
v___x_1508_ = l_Lean_mkAppN(v___x_1506_, v___x_1507_);
lean_dec_ref(v___x_1507_);
if (v_hasTrace_1494_ == 0)
{
lean_dec(v_cls_1482_);
v___y_1510_ = v___y_1485_;
v___y_1511_ = v___y_1486_;
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
v___y_1514_ = v___y_1489_;
v___y_1515_ = v___y_1490_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
lean_inc(v_cls_1482_);
v___x_1565_ = l_Lean_Name_append(v___x_1564_, v_cls_1482_);
v___x_1566_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1493_, v_options_1492_, v___x_1565_);
lean_dec(v___x_1565_);
if (v___x_1566_ == 0)
{
lean_dec(v_cls_1482_);
v___y_1510_ = v___y_1485_;
v___y_1511_ = v___y_1486_;
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
v___y_1514_ = v___y_1489_;
v___y_1515_ = v___y_1490_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1567_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__2);
lean_inc(v_name_1480_);
v___x_1568_ = l_Lean_MessageData_ofName(v_name_1480_);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__4);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
lean_inc_ref(v___x_1508_);
v___x_1572_ = l_Lean_MessageData_ofExpr(v___x_1508_);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1482_, v___x_1573_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_dec_ref_known(v___x_1574_, 1);
v___y_1510_ = v___y_1485_;
v___y_1511_ = v___y_1486_;
v___y_1512_ = v___y_1487_;
v___y_1513_ = v___y_1488_;
v___y_1514_ = v___y_1489_;
v___y_1515_ = v___y_1490_;
goto v___jp_1509_;
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_dec_ref(v___x_1508_);
lean_dec(v___x_1504_);
lean_dec(v_name_1480_);
lean_dec(v___x_1478_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1574_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1574_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
v___jp_1509_:
{
lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1508_);
v___x_1517_ = 0;
v___x_1518_ = lean_box(0);
v___x_1519_ = l_Lean_Meta_mkFreshExprMVar(v___x_1516_, v___x_1517_, v___x_1518_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref_known(v___x_1519_, 1);
v___x_1521_ = l_Lean_Expr_mvarId_x21(v_a_1520_);
lean_inc(v___x_1521_);
v___x_1522_ = l_Lean_MVarId_getType(v___x_1521_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___x_1524_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
v___x_1525_ = l_Lean_Name_append(v___x_1504_, v___x_1524_);
lean_inc(v___x_1478_);
v___x_1526_ = l_Lean_mkConst(v___x_1525_, v___x_1478_);
v___x_1527_ = l_Lean_mkAppN(v___x_1526_, v___x_1479_);
v___x_1528_ = 0;
v___x_1529_ = 1;
v___x_1530_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq___closed__0));
lean_inc(v___x_1521_);
v___x_1531_ = l_Lean_MVarId_rewrite(v___x_1521_, v_a_1523_, v___x_1527_, v___x_1528_, v___x_1530_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v_eNew_1533_; lean_object* v_eqProof_1534_; lean_object* v___x_1535_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v___x_1531_, 1);
v_eNew_1533_ = lean_ctor_get(v_a_1532_, 0);
lean_inc_ref(v_eNew_1533_);
v_eqProof_1534_ = lean_ctor_get(v_a_1532_, 1);
lean_inc_ref(v_eqProof_1534_);
lean_dec(v_a_1532_);
v___x_1535_ = l_Lean_MVarId_replaceTargetEq(v___x_1521_, v_eNew_1533_, v_eqProof_1534_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v_a_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = l_Lean_mkConst(v_name_1480_, v___x_1478_);
v___x_1538_ = l_Lean_mkAppN(v___x_1537_, v___x_1479_);
v___x_1539_ = l_Lean_mkAppN(v___x_1538_, v___x_1481_);
v___x_1540_ = l_Lean_mkAppN(v___x_1539_, v_fields_1483_);
v___x_1541_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_a_1536_, v___x_1540_, v___y_1513_);
lean_dec_ref(v___x_1541_);
v___x_1542_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_a_1520_, v___y_1513_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = 1;
v___x_1545_ = l_Lean_Meta_mkLambdaFVars(v_fields_1483_, v_a_1543_, v___x_1528_, v___x_1529_, v___x_1528_, v___x_1529_, v___x_1544_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = l_Lean_Meta_mkLambdaFVars(v___x_1479_, v_a_1546_, v___x_1528_, v___x_1529_, v___x_1528_, v___x_1529_, v___x_1544_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1547_;
}
else
{
return v___x_1545_;
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
lean_dec(v_a_1520_);
lean_dec(v_name_1480_);
lean_dec(v___x_1478_);
v_a_1548_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1535_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1535_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1563_; 
lean_dec(v___x_1521_);
lean_dec(v_a_1520_);
lean_dec(v_name_1480_);
lean_dec(v___x_1478_);
v_a_1556_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1558_ = v___x_1531_;
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1531_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1563_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v___x_1561_; 
if (v_isShared_1559_ == 0)
{
v___x_1561_ = v___x_1558_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_dec(v___x_1521_);
lean_dec(v_a_1520_);
lean_dec(v___x_1504_);
lean_dec(v_name_1480_);
lean_dec(v___x_1478_);
return v___x_1522_;
}
}
else
{
lean_dec(v___x_1504_);
lean_dec(v_name_1480_);
lean_dec(v___x_1478_);
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed(lean_object** _args){
lean_object* v_numParams_1583_ = _args[0];
lean_object* v___x_1584_ = _args[1];
lean_object* v_name_1585_ = _args[2];
lean_object* v___x_1586_ = _args[3];
lean_object* v___x_1587_ = _args[4];
lean_object* v_name_1588_ = _args[5];
lean_object* v___x_1589_ = _args[6];
lean_object* v_cls_1590_ = _args[7];
lean_object* v_fields_1591_ = _args[8];
lean_object* v_bodyExpr_1592_ = _args[9];
lean_object* v___y_1593_ = _args[10];
lean_object* v___y_1594_ = _args[11];
lean_object* v___y_1595_ = _args[12];
lean_object* v___y_1596_ = _args[13];
lean_object* v___y_1597_ = _args[14];
lean_object* v___y_1598_ = _args[15];
lean_object* v___y_1599_ = _args[16];
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1(v_numParams_1583_, v___x_1584_, v_name_1585_, v___x_1586_, v___x_1587_, v_name_1588_, v___x_1589_, v_cls_1590_, v_fields_1591_, v_bodyExpr_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_fields_1591_);
lean_dec_ref(v___x_1589_);
lean_dec_ref(v___x_1587_);
lean_dec(v___x_1584_);
lean_dec(v_numParams_1583_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(lean_object* v___x_1601_, size_t v_sz_1602_, size_t v_i_1603_, lean_object* v_bs_1604_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = lean_usize_dec_lt(v_i_1603_, v_sz_1602_);
if (v___x_1605_ == 0)
{
return v_bs_1604_;
}
else
{
lean_object* v_v_1606_; lean_object* v___x_1607_; lean_object* v_bs_x27_1608_; lean_object* v___x_1609_; size_t v___x_1610_; size_t v___x_1611_; lean_object* v___x_1612_; 
v_v_1606_ = lean_array_uget(v_bs_1604_, v_i_1603_);
v___x_1607_ = lean_unsigned_to_nat(0u);
v_bs_x27_1608_ = lean_array_uset(v_bs_1604_, v_i_1603_, v___x_1607_);
v___x_1609_ = l_Lean_mkAppN(v_v_1606_, v___x_1601_);
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1603_, v___x_1610_);
v___x_1612_ = lean_array_uset(v_bs_x27_1608_, v_i_1603_, v___x_1609_);
v_i_1603_ = v___x_1611_;
v_bs_1604_ = v___x_1612_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2___boxed(lean_object* v___x_1614_, lean_object* v_sz_1615_, lean_object* v_i_1616_, lean_object* v_bs_1617_){
_start:
{
size_t v_sz_boxed_1618_; size_t v_i_boxed_1619_; lean_object* v_res_1620_; 
v_sz_boxed_1618_ = lean_unbox_usize(v_sz_1615_);
lean_dec(v_sz_1615_);
v_i_boxed_1619_ = lean_unbox_usize(v_i_1616_);
lean_dec(v_i_1616_);
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1614_, v_sz_boxed_1618_, v_i_boxed_1619_, v_bs_1617_);
lean_dec_ref(v___x_1614_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(lean_object* v___x_1621_, size_t v_sz_1622_, size_t v_i_1623_, lean_object* v_bs_1624_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_usize_dec_lt(v_i_1623_, v_sz_1622_);
if (v___x_1625_ == 0)
{
lean_dec(v___x_1621_);
return v_bs_1624_;
}
else
{
lean_object* v_v_1626_; lean_object* v___x_1627_; lean_object* v_bs_x27_1628_; lean_object* v___x_1629_; size_t v___x_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v_v_1626_ = lean_array_uget(v_bs_1624_, v_i_1623_);
v___x_1627_ = lean_unsigned_to_nat(0u);
v_bs_x27_1628_ = lean_array_uset(v_bs_1624_, v_i_1623_, v___x_1627_);
lean_inc(v___x_1621_);
v___x_1629_ = l_Lean_mkConst(v_v_1626_, v___x_1621_);
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = lean_usize_add(v_i_1623_, v___x_1630_);
v___x_1632_ = lean_array_uset(v_bs_x27_1628_, v_i_1623_, v___x_1629_);
v_i_1623_ = v___x_1631_;
v_bs_1624_ = v___x_1632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1___boxed(lean_object* v___x_1634_, lean_object* v_sz_1635_, lean_object* v_i_1636_, lean_object* v_bs_1637_){
_start:
{
size_t v_sz_boxed_1638_; size_t v_i_boxed_1639_; lean_object* v_res_1640_; 
v_sz_boxed_1638_ = lean_unbox_usize(v_sz_1635_);
lean_dec(v_sz_1635_);
v_i_boxed_1639_ = lean_unbox_usize(v_i_1636_);
lean_dec(v_i_1636_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1634_, v_sz_boxed_1638_, v_i_boxed_1639_, v_bs_1637_);
return v_res_1640_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__0));
v___x_1643_ = l_Lean_stringToMessageData(v___x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(lean_object* v___x_1644_, lean_object* v_numParams_1645_, lean_object* v___x_1646_, lean_object* v___x_1647_, size_t v___x_1648_, lean_object* v___x_1649_, lean_object* v_name_1650_, lean_object* v_name_1651_, lean_object* v_cls_1652_, lean_object* v___f_1653_, lean_object* v_levelParams_1654_, lean_object* v_ctorSyntax_1655_, lean_object* v_args_1656_, lean_object* v_body_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; size_t v_sz_1668_; lean_object* v___x_1669_; size_t v_sz_1670_; lean_object* v___x_1671_; lean_object* v___f_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; lean_object* v___x_1676_; 
lean_inc_n(v_numParams_1645_, 2);
v___x_1665_ = l_Array_extract___redArg(v_args_1656_, v___x_1644_, v_numParams_1645_);
v___x_1666_ = lean_array_get_size(v_args_1656_);
v___x_1667_ = l_Array_toSubarray___redArg(v_args_1656_, v_numParams_1645_, v___x_1666_);
v_sz_1668_ = lean_array_size(v___x_1646_);
lean_inc(v___x_1647_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__1(v___x_1647_, v_sz_1668_, v___x_1648_, v___x_1646_);
v_sz_1670_ = lean_array_size(v___x_1669_);
v___x_1671_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v___x_1665_, v_sz_1670_, v___x_1648_, v___x_1669_);
lean_inc(v_cls_1652_);
lean_inc_ref(v___x_1671_);
lean_inc(v_name_1651_);
v___f_1672_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1672_, 0, v_numParams_1645_);
lean_closure_set(v___f_1672_, 1, v___x_1649_);
lean_closure_set(v___f_1672_, 2, v_name_1650_);
lean_closure_set(v___f_1672_, 3, v___x_1647_);
lean_closure_set(v___f_1672_, 4, v___x_1665_);
lean_closure_set(v___f_1672_, 5, v_name_1651_);
lean_closure_set(v___f_1672_, 6, v___x_1671_);
lean_closure_set(v___f_1672_, 7, v_cls_1652_);
v___x_1673_ = l_Subarray_copy___redArg(v___x_1667_);
v___x_1674_ = l_Lean_Expr_replaceFVars(v_body_1657_, v___x_1673_, v___x_1671_);
lean_dec_ref(v___x_1671_);
lean_dec_ref(v___x_1673_);
v___x_1675_ = 0;
v___x_1676_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v___x_1674_, v___f_1672_, v___x_1675_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1678_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc_n(v_a_1677_, 2);
lean_dec_ref_known(v___x_1676_, 1);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
v___x_1678_ = lean_infer_type(v_a_1677_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___y_1681_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; lean_object* v___x_1703_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
lean_inc(v___y_1663_);
lean_inc_ref(v___y_1662_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
v___x_1703_ = lean_apply_7(v___f_1653_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_, lean_box(0));
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_a_1704_; uint8_t v___x_1705_; 
v_a_1704_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref_known(v___x_1703_, 1);
v___x_1705_ = lean_unbox(v_a_1704_);
lean_dec(v_a_1704_);
if (v___x_1705_ == 0)
{
lean_dec(v_cls_1652_);
v___y_1681_ = v___y_1658_;
v___y_1682_ = v___y_1659_;
v___y_1683_ = v___y_1660_;
v___y_1684_ = v___y_1661_;
v___y_1685_ = v___y_1662_;
v___y_1686_ = v___y_1663_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___closed__1);
lean_inc(v_a_1679_);
v___x_1707_ = l_Lean_MessageData_ofExpr(v_a_1679_);
v___x_1708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
v___x_1709_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1652_, v___x_1708_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_dec_ref_known(v___x_1709_, 1);
v___y_1681_ = v___y_1658_;
v___y_1682_ = v___y_1659_;
v___y_1683_ = v___y_1660_;
v___y_1684_ = v___y_1661_;
v___y_1685_ = v___y_1662_;
v___y_1686_ = v___y_1663_;
goto v___jp_1680_;
}
else
{
lean_dec(v_a_1679_);
lean_dec(v_a_1677_);
lean_dec(v_ctorSyntax_1655_);
lean_dec(v_levelParams_1654_);
lean_dec(v_name_1651_);
return v___x_1709_;
}
}
}
else
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
lean_dec(v_a_1679_);
lean_dec(v_a_1677_);
lean_dec(v_ctorSyntax_1655_);
lean_dec(v_levelParams_1654_);
lean_dec(v_cls_1652_);
lean_dec(v_name_1651_);
v_a_1710_ = lean_ctor_get(v___x_1703_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1703_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1703_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1703_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
v___jp_1680_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1702_; 
v___x_1687_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1651_);
v___x_1688_ = lean_box(0);
lean_inc(v_a_1677_);
v___x_1689_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v___x_1687_, v_levelParams_1654_, v_a_1679_, v_a_1677_, v___x_1688_, v___y_1686_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1702_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1702_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_addDecl(v___x_1695_, v___x_1675_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; 
lean_dec_ref_known(v___x_1696_, 1);
v___x_1697_ = lean_box(0);
v___x_1698_ = lean_box(0);
v___x_1699_ = 1;
v___x_1700_ = l_Lean_Elab_Term_addTermInfo_x27(v_ctorSyntax_1655_, v_a_1677_, v___x_1697_, v___x_1697_, v___x_1698_, v___x_1699_, v___x_1675_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
return v___x_1700_;
}
else
{
lean_dec(v_a_1677_);
lean_dec(v_ctorSyntax_1655_);
return v___x_1696_;
}
}
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v_a_1677_);
lean_dec(v_ctorSyntax_1655_);
lean_dec(v_levelParams_1654_);
lean_dec_ref(v___f_1653_);
lean_dec(v_cls_1652_);
lean_dec(v_name_1651_);
v_a_1718_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1678_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1678_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v_ctorSyntax_1655_);
lean_dec(v_levelParams_1654_);
lean_dec_ref(v___f_1653_);
lean_dec(v_cls_1652_);
lean_dec(v_name_1651_);
v_a_1726_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1676_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1676_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed(lean_object** _args){
lean_object* v___x_1734_ = _args[0];
lean_object* v_numParams_1735_ = _args[1];
lean_object* v___x_1736_ = _args[2];
lean_object* v___x_1737_ = _args[3];
lean_object* v___x_1738_ = _args[4];
lean_object* v___x_1739_ = _args[5];
lean_object* v_name_1740_ = _args[6];
lean_object* v_name_1741_ = _args[7];
lean_object* v_cls_1742_ = _args[8];
lean_object* v___f_1743_ = _args[9];
lean_object* v_levelParams_1744_ = _args[10];
lean_object* v_ctorSyntax_1745_ = _args[11];
lean_object* v_args_1746_ = _args[12];
lean_object* v_body_1747_ = _args[13];
lean_object* v___y_1748_ = _args[14];
lean_object* v___y_1749_ = _args[15];
lean_object* v___y_1750_ = _args[16];
lean_object* v___y_1751_ = _args[17];
lean_object* v___y_1752_ = _args[18];
lean_object* v___y_1753_ = _args[19];
lean_object* v___y_1754_ = _args[20];
_start:
{
size_t v___x_9129__boxed_1755_; lean_object* v_res_1756_; 
v___x_9129__boxed_1755_ = lean_unbox_usize(v___x_1738_);
lean_dec(v___x_1738_);
v_res_1756_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2(v___x_1734_, v_numParams_1735_, v___x_1736_, v___x_1737_, v___x_9129__boxed_1755_, v___x_1739_, v_name_1740_, v_name_1741_, v_cls_1742_, v___f_1743_, v_levelParams_1744_, v_ctorSyntax_1745_, v_args_1746_, v_body_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v_body_1747_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(size_t v_sz_1757_, size_t v_i_1758_, lean_object* v_bs_1759_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_lt(v_i_1758_, v_sz_1757_);
if (v___x_1760_ == 0)
{
return v_bs_1759_;
}
else
{
lean_object* v_v_1761_; lean_object* v_toConstantVal_1762_; lean_object* v_name_1763_; lean_object* v___x_1764_; lean_object* v_bs_x27_1765_; lean_object* v___x_1766_; size_t v___x_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v_v_1761_ = lean_array_uget_borrowed(v_bs_1759_, v_i_1758_);
v_toConstantVal_1762_ = lean_ctor_get(v_v_1761_, 0);
v_name_1763_ = lean_ctor_get(v_toConstantVal_1762_, 0);
lean_inc(v_name_1763_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v_bs_x27_1765_ = lean_array_uset(v_bs_1759_, v_i_1758_, v___x_1764_);
v___x_1766_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_1763_);
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1758_, v___x_1767_);
v___x_1769_ = lean_array_uset(v_bs_x27_1765_, v_i_1758_, v___x_1766_);
v_i_1758_ = v___x_1768_;
v_bs_1759_ = v___x_1769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0___boxed(lean_object* v_sz_1771_, lean_object* v_i_1772_, lean_object* v_bs_1773_){
_start:
{
size_t v_sz_boxed_1774_; size_t v_i_boxed_1775_; lean_object* v_res_1776_; 
v_sz_boxed_1774_ = lean_unbox_usize(v_sz_1771_);
lean_dec(v_sz_1771_);
v_i_boxed_1775_ = lean_unbox_usize(v_i_1772_);
lean_dec(v_i_1772_);
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_boxed_1774_, v_i_boxed_1775_, v_bs_1773_);
return v_res_1776_;
}
}
static lean_object* _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__1));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(lean_object* v_infos_1784_, lean_object* v_ctorSyntax_1785_, lean_object* v_numParams_1786_, lean_object* v_name_1787_, lean_object* v_ctor_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_cls_1796_; lean_object* v___f_1797_; lean_object* v___x_1798_; lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1841_; 
v_cls_1796_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___f_1797_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__0));
v___x_1798_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1796_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1841_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1841_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; uint8_t v___x_1833_; 
v___x_1803_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1833_ = lean_unbox(v_a_1799_);
lean_dec(v_a_1799_);
if (v___x_1833_ == 0)
{
v___y_1805_ = v_a_1789_;
v___y_1806_ = v_a_1790_;
v___y_1807_ = v_a_1791_;
v___y_1808_ = v_a_1792_;
v___y_1809_ = v_a_1793_;
v___y_1810_ = v_a_1794_;
goto v___jp_1804_;
}
else
{
lean_object* v_toConstantVal_1834_; lean_object* v_name_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v_toConstantVal_1834_ = lean_ctor_get(v_ctor_1788_, 0);
v_name_1835_ = lean_ctor_get(v_toConstantVal_1834_, 0);
v___x_1836_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___closed__2);
lean_inc(v_name_1835_);
v___x_1837_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v_name_1835_);
v___x_1838_ = l_Lean_MessageData_ofName(v___x_1837_);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1836_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1796_, v___x_1839_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_dec_ref_known(v___x_1840_, 1);
v___y_1805_ = v_a_1789_;
v___y_1806_ = v_a_1790_;
v___y_1807_ = v_a_1791_;
v___y_1808_ = v_a_1792_;
v___y_1809_ = v_a_1793_;
v___y_1810_ = v_a_1794_;
goto v___jp_1804_;
}
else
{
lean_del_object(v___x_1801_);
lean_dec_ref(v_ctor_1788_);
lean_dec(v_name_1787_);
lean_dec(v_numParams_1786_);
lean_dec(v_ctorSyntax_1785_);
lean_dec_ref(v_infos_1784_);
return v___x_1840_;
}
}
v___jp_1804_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_toConstantVal_1813_; lean_object* v_toConstantVal_1814_; lean_object* v_levelParams_1815_; lean_object* v_name_1816_; lean_object* v_levelParams_1817_; lean_object* v_type_1818_; lean_object* v___x_1819_; size_t v_sz_1820_; size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___f_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = lean_array_get_borrowed(v___x_1803_, v_infos_1784_, v___x_1811_);
v_toConstantVal_1813_ = lean_ctor_get(v___x_1812_, 0);
v_toConstantVal_1814_ = lean_ctor_get(v_ctor_1788_, 0);
lean_inc_ref(v_toConstantVal_1814_);
lean_dec_ref(v_ctor_1788_);
v_levelParams_1815_ = lean_ctor_get(v_toConstantVal_1813_, 1);
lean_inc(v_levelParams_1815_);
v_name_1816_ = lean_ctor_get(v_toConstantVal_1814_, 0);
lean_inc(v_name_1816_);
v_levelParams_1817_ = lean_ctor_get(v_toConstantVal_1814_, 1);
lean_inc(v_levelParams_1817_);
v_type_1818_ = lean_ctor_get(v_toConstantVal_1814_, 2);
lean_inc_ref(v_type_1818_);
lean_dec_ref(v_toConstantVal_1814_);
v___x_1819_ = lean_array_get_size(v_infos_1784_);
v_sz_1820_ = lean_array_size(v_infos_1784_);
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__0(v_sz_1820_, v___x_1821_, v_infos_1784_);
v___x_1823_ = lean_box(0);
v___x_1824_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_1815_, v___x_1823_);
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_numParams_1786_);
v___f_1826_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__2___boxed), 21, 12);
lean_closure_set(v___f_1826_, 0, v___x_1811_);
lean_closure_set(v___f_1826_, 1, v_numParams_1786_);
lean_closure_set(v___f_1826_, 2, v___x_1822_);
lean_closure_set(v___f_1826_, 3, v___x_1824_);
lean_closure_set(v___f_1826_, 4, v___x_1825_);
lean_closure_set(v___f_1826_, 5, v___x_1819_);
lean_closure_set(v___f_1826_, 6, v_name_1787_);
lean_closure_set(v___f_1826_, 7, v_name_1816_);
lean_closure_set(v___f_1826_, 8, v_cls_1796_);
lean_closure_set(v___f_1826_, 9, v___f_1797_);
lean_closure_set(v___f_1826_, 10, v_levelParams_1817_);
lean_closure_set(v___f_1826_, 11, v_ctorSyntax_1785_);
v___x_1827_ = lean_nat_add(v_numParams_1786_, v___x_1819_);
lean_dec(v_numParams_1786_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set_tag(v___x_1801_, 1);
lean_ctor_set(v___x_1801_, 0, v___x_1827_);
v___x_1829_ = v___x_1801_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
uint8_t v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = 0;
v___x_1831_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1818_, v___x_1829_, v___f_1826_, v___x_1830_, v___x_1830_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed(lean_object* v_infos_1842_, lean_object* v_ctorSyntax_1843_, lean_object* v_numParams_1844_, lean_object* v_name_1845_, lean_object* v_ctor_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_1842_, v_ctorSyntax_1843_, v_numParams_1844_, v_name_1845_, v_ctor_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(lean_object* v_mvarId_1855_, lean_object* v_val_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(v_mvarId_1855_, v_val_1856_, v___y_1860_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___boxed(lean_object* v_mvarId_1865_, lean_object* v_val_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3(v_mvarId_1865_, v_val_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(lean_object* v_cls_1875_, lean_object* v_msg_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_1875_, v_msg_1876_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___boxed(lean_object* v_cls_1885_, lean_object* v_msg_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5(v_cls_1885_, v_msg_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
lean_dec(v___y_1892_);
lean_dec_ref(v___y_1891_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
return v_res_1894_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_instMonadEIO(lean_box(0));
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(lean_object* v_msg_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v_toApplicative_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_2003_; 
v___x_1910_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__0);
v___x_1911_ = l_StateRefT_x27_instMonad___redArg(v___x_1910_);
v_toApplicative_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v___x_1911_, 1);
lean_dec(v_unused_2004_);
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_2003_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_toApplicative_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_2003_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v_toFunctor_1916_; lean_object* v_toSeq_1917_; lean_object* v_toSeqLeft_1918_; lean_object* v_toSeqRight_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_2001_; 
v_toFunctor_1916_ = lean_ctor_get(v_toApplicative_1912_, 0);
v_toSeq_1917_ = lean_ctor_get(v_toApplicative_1912_, 2);
v_toSeqLeft_1918_ = lean_ctor_get(v_toApplicative_1912_, 3);
v_toSeqRight_1919_ = lean_ctor_get(v_toApplicative_1912_, 4);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_toApplicative_1912_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v_toApplicative_1912_, 1);
lean_dec(v_unused_2002_);
v___x_1921_ = v_toApplicative_1912_;
v_isShared_1922_ = v_isSharedCheck_2001_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_toSeqRight_1919_);
lean_inc(v_toSeqLeft_1918_);
lean_inc(v_toSeq_1917_);
lean_inc(v_toFunctor_1916_);
lean_dec(v_toApplicative_1912_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_2001_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___f_1923_; lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___f_1930_; lean_object* v___x_1932_; 
v___f_1923_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__1));
v___f_1924_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1916_);
v___f_1925_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1925_, 0, v_toFunctor_1916_);
v___f_1926_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1926_, 0, v_toFunctor_1916_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___f_1925_);
lean_ctor_set(v___x_1927_, 1, v___f_1926_);
v___f_1928_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1928_, 0, v_toSeqRight_1919_);
v___f_1929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1929_, 0, v_toSeqLeft_1918_);
v___f_1930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1930_, 0, v_toSeq_1917_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 4, v___f_1928_);
lean_ctor_set(v___x_1921_, 3, v___f_1929_);
lean_ctor_set(v___x_1921_, 2, v___f_1930_);
lean_ctor_set(v___x_1921_, 1, v___f_1923_);
lean_ctor_set(v___x_1921_, 0, v___x_1927_);
v___x_1932_ = v___x_1921_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___f_1923_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v___f_1930_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v___f_1929_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v___f_1928_);
v___x_1932_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1934_; 
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v___f_1924_);
lean_ctor_set(v___x_1914_, 0, v___x_1932_);
v___x_1934_ = v___x_1914_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v___f_1924_);
v___x_1934_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v_toApplicative_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1997_; 
v___x_1935_ = l_StateRefT_x27_instMonad___redArg(v___x_1934_);
v_toApplicative_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v___x_1935_, 1);
lean_dec(v_unused_1998_);
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1997_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_toApplicative_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1997_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v_toFunctor_1940_; lean_object* v_toSeq_1941_; lean_object* v_toSeqLeft_1942_; lean_object* v_toSeqRight_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1995_; 
v_toFunctor_1940_ = lean_ctor_get(v_toApplicative_1936_, 0);
v_toSeq_1941_ = lean_ctor_get(v_toApplicative_1936_, 2);
v_toSeqLeft_1942_ = lean_ctor_get(v_toApplicative_1936_, 3);
v_toSeqRight_1943_ = lean_ctor_get(v_toApplicative_1936_, 4);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_toApplicative_1936_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v_toApplicative_1936_, 1);
lean_dec(v_unused_1996_);
v___x_1945_ = v_toApplicative_1936_;
v_isShared_1946_ = v_isSharedCheck_1995_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_toSeqRight_1943_);
lean_inc(v_toSeqLeft_1942_);
lean_inc(v_toSeq_1941_);
lean_inc(v_toFunctor_1940_);
lean_dec(v_toApplicative_1936_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1995_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___f_1954_; lean_object* v___x_1956_; 
v___f_1947_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__3));
v___f_1948_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1940_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toFunctor_1940_);
v___f_1950_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1950_, 0, v_toFunctor_1940_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___f_1949_);
lean_ctor_set(v___x_1951_, 1, v___f_1950_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toSeqRight_1943_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeqLeft_1942_);
v___f_1954_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1954_, 0, v_toSeq_1941_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 4, v___f_1952_);
lean_ctor_set(v___x_1945_, 3, v___f_1953_);
lean_ctor_set(v___x_1945_, 2, v___f_1954_);
lean_ctor_set(v___x_1945_, 1, v___f_1947_);
lean_ctor_set(v___x_1945_, 0, v___x_1951_);
v___x_1956_ = v___x_1945_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v___f_1947_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v___f_1954_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v___f_1953_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v___f_1952_);
v___x_1956_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
lean_object* v___x_1958_; 
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 1, v___f_1948_);
lean_ctor_set(v___x_1938_, 0, v___x_1956_);
v___x_1958_ = v___x_1938_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___f_1948_);
v___x_1958_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
lean_object* v___x_1959_; lean_object* v_toApplicative_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1991_; 
v___x_1959_ = l_StateRefT_x27_instMonad___redArg(v___x_1958_);
v_toApplicative_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v___x_1959_, 1);
lean_dec(v_unused_1992_);
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_1991_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_toApplicative_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1991_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_toFunctor_1964_; lean_object* v_toSeq_1965_; lean_object* v_toSeqLeft_1966_; lean_object* v_toSeqRight_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1989_; 
v_toFunctor_1964_ = lean_ctor_get(v_toApplicative_1960_, 0);
v_toSeq_1965_ = lean_ctor_get(v_toApplicative_1960_, 2);
v_toSeqLeft_1966_ = lean_ctor_get(v_toApplicative_1960_, 3);
v_toSeqRight_1967_ = lean_ctor_get(v_toApplicative_1960_, 4);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_toApplicative_1960_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; 
v_unused_1990_ = lean_ctor_get(v_toApplicative_1960_, 1);
lean_dec(v_unused_1990_);
v___x_1969_ = v_toApplicative_1960_;
v_isShared_1970_ = v_isSharedCheck_1989_;
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
v_isShared_1970_ = v_isSharedCheck_1989_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___f_1971_; lean_object* v___f_1972_; lean_object* v___f_1973_; lean_object* v___f_1974_; lean_object* v___x_1975_; lean_object* v___f_1976_; lean_object* v___f_1977_; lean_object* v___f_1978_; lean_object* v___x_1980_; 
v___f_1971_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__5));
v___f_1972_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___closed__6));
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
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1975_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v___f_1971_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v___f_1978_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v___f_1977_);
lean_ctor_set(v_reuseFailAlloc_1988_, 4, v___f_1976_);
v___x_1980_ = v_reuseFailAlloc_1988_;
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
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v___f_1972_);
v___x_1982_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_3780__overap_1985_; lean_object* v___x_1986_; 
v___x_1983_ = lean_box(0);
v___x_1984_ = l_instInhabitedOfMonad___redArg(v___x_1982_, v___x_1983_);
v___x_3780__overap_1985_ = lean_panic_fn_borrowed(v___x_1984_, v_msg_1902_);
lean_dec(v___x_1984_);
lean_inc(v___y_1908_);
lean_inc_ref(v___y_1907_);
lean_inc(v___y_1906_);
lean_inc_ref(v___y_1905_);
lean_inc(v___y_1904_);
lean_inc_ref(v___y_1903_);
v___x_1986_ = lean_apply_7(v___x_3780__overap_1985_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_, lean_box(0));
return v___x_1986_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1___boxed(lean_object* v_msg_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v_msg_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
lean_dec(v___y_2011_);
lean_dec_ref(v___y_2010_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
lean_dec(v___y_2007_);
lean_dec_ref(v___y_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(lean_object* v_opts_2014_, lean_object* v_opt_2015_){
_start:
{
lean_object* v_name_2016_; lean_object* v_defValue_2017_; lean_object* v_map_2018_; lean_object* v___x_2019_; 
v_name_2016_ = lean_ctor_get(v_opt_2015_, 0);
v_defValue_2017_ = lean_ctor_get(v_opt_2015_, 1);
v_map_2018_ = lean_ctor_get(v_opts_2014_, 0);
v___x_2019_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2018_, v_name_2016_);
if (lean_obj_tag(v___x_2019_) == 0)
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_unbox(v_defValue_2017_);
return v___x_2020_;
}
else
{
lean_object* v_val_2021_; 
v_val_2021_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v___x_2019_, 1);
if (lean_obj_tag(v_val_2021_) == 1)
{
uint8_t v_v_2022_; 
v_v_2022_ = lean_ctor_get_uint8(v_val_2021_, 0);
lean_dec_ref_known(v_val_2021_, 0);
return v_v_2022_;
}
else
{
uint8_t v___x_2023_; 
lean_dec(v_val_2021_);
v___x_2023_ = lean_unbox(v_defValue_2017_);
return v___x_2023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_2024_, lean_object* v_opt_2025_){
_start:
{
uint8_t v_res_2026_; lean_object* v_r_2027_; 
v_res_2026_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_opts_2024_, v_opt_2025_);
lean_dec_ref(v_opt_2025_);
lean_dec_ref(v_opts_2024_);
v_r_2027_ = lean_box(v_res_2026_);
return v_r_2027_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_box(1);
v___x_2029_ = l_Lean_MessageData_ofFormat(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__2));
v___x_2034_ = l_Lean_MessageData_ofFormat(v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
if (lean_obj_tag(v_x_2036_) == 0)
{
return v_x_2035_;
}
else
{
lean_object* v_head_2037_; lean_object* v_tail_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2060_; 
v_head_2037_ = lean_ctor_get(v_x_2036_, 0);
v_tail_2038_ = lean_ctor_get(v_x_2036_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_x_2036_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2040_ = v_x_2036_;
v_isShared_2041_ = v_isSharedCheck_2060_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_tail_2038_);
lean_inc(v_head_2037_);
lean_dec(v_x_2036_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2060_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_before_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2058_; 
v_before_2042_ = lean_ctor_get(v_head_2037_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_head_2037_);
if (v_isSharedCheck_2058_ == 0)
{
lean_object* v_unused_2059_; 
v_unused_2059_ = lean_ctor_get(v_head_2037_, 1);
lean_dec(v_unused_2059_);
v___x_2044_ = v_head_2037_;
v_isShared_2045_ = v_isSharedCheck_2058_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_before_2042_);
lean_dec(v_head_2037_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2058_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_2045_ == 0)
{
lean_ctor_set_tag(v___x_2044_, 7);
lean_ctor_set(v___x_2044_, 1, v___x_2046_);
lean_ctor_set(v___x_2044_, 0, v_x_2035_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_x_2035_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
v___x_2049_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 7);
lean_ctor_set(v___x_2040_, 1, v___x_2049_);
lean_ctor_set(v___x_2040_, 0, v___x_2048_);
v___x_2051_ = v___x_2040_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = l_Lean_MessageData_ofSyntax(v_before_2042_);
v___x_2053_ = l_Lean_indentD(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2051_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v_x_2035_ = v___x_2054_;
v_x_2036_ = v_tail_2038_;
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
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__1));
v___x_2065_ = l_Lean_MessageData_ofFormat(v___x_2064_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(lean_object* v_msgData_2066_, lean_object* v_macroStack_2067_, lean_object* v___y_2068_){
_start:
{
lean_object* v_options_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_options_2070_ = lean_ctor_get(v___y_2068_, 2);
v___x_2071_ = l_Lean_Elab_pp_macroStack;
v___x_2072_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_options_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_object* v___x_2073_; 
lean_dec(v_macroStack_2067_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v_msgData_2066_);
return v___x_2073_;
}
else
{
if (lean_obj_tag(v_macroStack_2067_) == 0)
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_msgData_2066_);
return v___x_2074_;
}
else
{
lean_object* v_head_2075_; lean_object* v_after_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2091_; 
v_head_2075_ = lean_ctor_get(v_macroStack_2067_, 0);
lean_inc(v_head_2075_);
v_after_2076_ = lean_ctor_get(v_head_2075_, 1);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_head_2075_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v_head_2075_, 0);
lean_dec(v_unused_2092_);
v___x_2078_ = v_head_2075_;
v_isShared_2079_ = v_isSharedCheck_2091_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_after_2076_);
lean_dec(v_head_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2091_;
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
lean_ctor_set(v___x_2078_, 0, v_msgData_2066_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_msgData_2066_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_msgData_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2083_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_2084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2082_);
lean_ctor_set(v___x_2084_, 1, v___x_2083_);
v___x_2085_ = l_Lean_MessageData_ofSyntax(v_after_2076_);
v___x_2086_ = l_Lean_indentD(v___x_2085_);
v_msgData_2087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_2087_, 0, v___x_2084_);
lean_ctor_set(v_msgData_2087_, 1, v___x_2086_);
v___x_2088_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__6(v_msgData_2087_, v_macroStack_2067_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_2093_, lean_object* v_macroStack_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2093_, v_macroStack_2094_, v___y_2095_);
lean_dec_ref(v___y_2095_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(lean_object* v_msg_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_ref_2106_; lean_object* v___x_2107_; lean_object* v_a_2108_; lean_object* v_macroStack_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2120_; 
v_ref_2106_ = lean_ctor_get(v___y_2103_, 5);
v___x_2107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2098_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref(v___x_2107_);
v_macroStack_2109_ = lean_ctor_get(v___y_2099_, 1);
v___x_2110_ = l_Lean_Elab_getBetterRef(v_ref_2106_, v_macroStack_2109_);
lean_inc(v_macroStack_2109_);
v___x_2111_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2108_, v_macroStack_2109_, v___y_2103_);
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2120_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2120_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2110_);
lean_ctor_set(v___x_2116_, 1, v_a_2112_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 1);
lean_ctor_set(v___x_2114_, 0, v___x_2116_);
v___x_2118_ = v___x_2114_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg___boxed(lean_object* v_msg_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2129_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
v___x_2131_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__0));
v___x_2132_ = l_Lean_stringToMessageData(v___x_2131_);
return v___x_2132_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__2));
v___x_2135_ = l_Lean_stringToMessageData(v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2139_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__6));
v___x_2140_ = lean_unsigned_to_nat(11u);
v___x_2141_ = lean_unsigned_to_nat(122u);
v___x_2142_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__5));
v___x_2143_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__4));
v___x_2144_ = l_mkPanicMessageWithDecl(v___x_2143_, v___x_2142_, v___x_2141_, v___x_2140_, v___x_2139_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(lean_object* v_constName_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2161_; lean_object* v_env_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; 
v___x_2161_ = lean_st_ref_get(v___y_2151_);
v_env_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc_ref(v_env_2162_);
lean_dec(v___x_2161_);
v___x_2163_ = 0;
lean_inc(v_constName_2145_);
v___x_2164_ = l_Lean_Environment_findAsync_x3f(v_env_2162_, v_constName_2145_, v___x_2163_);
if (lean_obj_tag(v___x_2164_) == 1)
{
lean_object* v_val_2165_; uint8_t v_kind_2166_; 
v_val_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_val_2165_);
lean_dec_ref_known(v___x_2164_, 1);
v_kind_2166_ = lean_ctor_get_uint8(v_val_2165_, sizeof(void*)*3);
if (v_kind_2166_ == 6)
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2165_);
if (lean_obj_tag(v___x_2167_) == 6)
{
lean_object* v_val_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2175_; 
lean_dec(v_constName_2145_);
v_val_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_val_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2175_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2173_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set_tag(v___x_2170_, 0);
v___x_2173_ = v___x_2170_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_val_2168_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v___x_2167_);
v___x_2176_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__7);
v___x_2177_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__1(v___x_2176_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2186_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2180_ = v___x_2177_;
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2177_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
if (lean_obj_tag(v_a_2178_) == 0)
{
lean_del_object(v___x_2180_);
goto v___jp_2153_;
}
else
{
lean_object* v_val_2182_; lean_object* v___x_2184_; 
lean_dec(v_constName_2145_);
v_val_2182_ = lean_ctor_get(v_a_2178_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v_a_2178_, 1);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v_val_2182_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_val_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2194_; 
lean_dec(v_constName_2145_);
v_a_2187_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2189_ = v___x_2177_;
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_a_2187_);
lean_dec(v___x_2177_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2194_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2192_; 
if (v_isShared_2190_ == 0)
{
v___x_2192_ = v___x_2189_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2187_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
else
{
lean_dec(v_val_2165_);
goto v___jp_2153_;
}
}
else
{
lean_dec(v___x_2164_);
goto v___jp_2153_;
}
v___jp_2153_:
{
lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2154_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2155_ = 0;
v___x_2156_ = l_Lean_MessageData_ofConstName(v_constName_2145_, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2154_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__3);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v___x_2159_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2160_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___boxed(lean_object* v_constName_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_constName_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(lean_object* v_a_2204_, lean_object* v_infos_2205_, lean_object* v_numParams_2206_, lean_object* v_as_x27_2207_, lean_object* v_b_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
if (lean_obj_tag(v_as_x27_2207_) == 0)
{
lean_object* v___x_2216_; 
lean_dec(v_numParams_2206_);
lean_dec_ref(v_infos_2205_);
lean_dec_ref(v_a_2204_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v_b_2208_);
return v___x_2216_;
}
else
{
lean_object* v_head_2217_; lean_object* v_tail_2218_; lean_object* v_array_2219_; lean_object* v_start_2220_; lean_object* v_stop_2221_; uint8_t v___x_2222_; 
v_head_2217_ = lean_ctor_get(v_as_x27_2207_, 0);
v_tail_2218_ = lean_ctor_get(v_as_x27_2207_, 1);
v_array_2219_ = lean_ctor_get(v_b_2208_, 0);
v_start_2220_ = lean_ctor_get(v_b_2208_, 1);
v_stop_2221_ = lean_ctor_get(v_b_2208_, 2);
v___x_2222_ = lean_nat_dec_lt(v_start_2220_, v_stop_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec(v_numParams_2206_);
lean_dec_ref(v_infos_2205_);
lean_dec_ref(v_a_2204_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_b_2208_);
return v___x_2223_;
}
else
{
lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2255_; 
lean_inc(v_stop_2221_);
lean_inc(v_start_2220_);
lean_inc_ref(v_array_2219_);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_b_2208_);
if (v_isSharedCheck_2255_ == 0)
{
lean_object* v_unused_2256_; lean_object* v_unused_2257_; lean_object* v_unused_2258_; 
v_unused_2256_ = lean_ctor_get(v_b_2208_, 2);
lean_dec(v_unused_2256_);
v_unused_2257_ = lean_ctor_get(v_b_2208_, 1);
lean_dec(v_unused_2257_);
v_unused_2258_ = lean_ctor_get(v_b_2208_, 0);
lean_dec(v_unused_2258_);
v___x_2225_ = v_b_2208_;
v_isShared_2226_ = v_isSharedCheck_2255_;
goto v_resetjp_2224_;
}
else
{
lean_dec(v_b_2208_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2255_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; 
lean_inc(v_head_2217_);
v___x_2227_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2217_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_toConstantVal_2228_; lean_object* v_a_2229_; lean_object* v_name_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v_toConstantVal_2228_ = lean_ctor_get(v_a_2204_, 0);
v_a_2229_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2227_, 1);
v_name_2230_ = lean_ctor_get(v_toConstantVal_2228_, 0);
v___x_2231_ = lean_array_fget_borrowed(v_array_2219_, v_start_2220_);
lean_inc(v_name_2230_);
lean_inc(v_numParams_2206_);
lean_inc(v___x_2231_);
lean_inc_ref(v_infos_2205_);
v___x_2232_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2205_, v___x_2231_, v_numParams_2206_, v_name_2230_, v_a_2229_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
lean_dec_ref_known(v___x_2232_, 1);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_add(v_start_2220_, v___x_2233_);
lean_dec(v_start_2220_);
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 1, v___x_2234_);
v___x_2236_ = v___x_2225_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_array_2219_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_stop_2221_);
v___x_2236_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v_as_x27_2207_ = v_tail_2218_;
v_b_2208_ = v___x_2236_;
goto _start;
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_del_object(v___x_2225_);
lean_dec(v_stop_2221_);
lean_dec(v_start_2220_);
lean_dec_ref(v_array_2219_);
lean_dec(v_numParams_2206_);
lean_dec_ref(v_infos_2205_);
lean_dec_ref(v_a_2204_);
v_a_2239_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2232_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2232_);
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
lean_del_object(v___x_2225_);
lean_dec(v_stop_2221_);
lean_dec(v_start_2220_);
lean_dec_ref(v_array_2219_);
lean_dec(v_numParams_2206_);
lean_dec_ref(v_infos_2205_);
lean_dec_ref(v_a_2204_);
v_a_2247_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2227_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2227_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg___boxed(lean_object* v_a_2259_, lean_object* v_infos_2260_, lean_object* v_numParams_2261_, lean_object* v_as_x27_2262_, lean_object* v_b_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2259_, v_infos_2260_, v_numParams_2261_, v_as_x27_2262_, v_b_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v_as_x27_2262_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(lean_object* v_infos_2272_, lean_object* v_numParams_2273_, lean_object* v_as_2274_, size_t v_sz_2275_, size_t v_i_2276_, lean_object* v_b_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_usize_dec_lt(v_i_2276_, v_sz_2275_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2286_; 
lean_dec(v_numParams_2273_);
lean_dec_ref(v_infos_2272_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v_b_2277_);
return v___x_2286_;
}
else
{
lean_object* v_array_2287_; lean_object* v_start_2288_; lean_object* v_stop_2289_; uint8_t v___x_2290_; 
v_array_2287_ = lean_ctor_get(v_b_2277_, 0);
v_start_2288_ = lean_ctor_get(v_b_2277_, 1);
v_stop_2289_ = lean_ctor_get(v_b_2277_, 2);
v___x_2290_ = lean_nat_dec_lt(v_start_2288_, v_stop_2289_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; 
lean_dec(v_numParams_2273_);
lean_dec_ref(v_infos_2272_);
v___x_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2291_, 0, v_b_2277_);
return v___x_2291_;
}
else
{
lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2319_; 
lean_inc(v_stop_2289_);
lean_inc(v_start_2288_);
lean_inc_ref(v_array_2287_);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_b_2277_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; lean_object* v_unused_2321_; lean_object* v_unused_2322_; 
v_unused_2320_ = lean_ctor_get(v_b_2277_, 2);
lean_dec(v_unused_2320_);
v_unused_2321_ = lean_ctor_get(v_b_2277_, 1);
lean_dec(v_unused_2321_);
v_unused_2322_ = lean_ctor_get(v_b_2277_, 0);
lean_dec(v_unused_2322_);
v___x_2293_ = v_b_2277_;
v_isShared_2294_ = v_isSharedCheck_2319_;
goto v_resetjp_2292_;
}
else
{
lean_dec(v_b_2277_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2319_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v_ctorSyntax_2296_; lean_object* v_a_2297_; lean_object* v_ctors_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2295_ = lean_array_fget_borrowed(v_array_2287_, v_start_2288_);
v_ctorSyntax_2296_ = lean_ctor_get(v___x_2295_, 4);
v_a_2297_ = lean_array_uget_borrowed(v_as_2274_, v_i_2276_);
v_ctors_2298_ = lean_ctor_get(v_a_2297_, 4);
v___x_2299_ = lean_array_get_size(v_ctorSyntax_2296_);
v___x_2300_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ctorSyntax_2296_);
v___x_2301_ = l_Array_toSubarray___redArg(v_ctorSyntax_2296_, v___x_2300_, v___x_2299_);
lean_inc(v_numParams_2273_);
lean_inc_ref(v_infos_2272_);
lean_inc(v_a_2297_);
v___x_2302_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2297_, v_infos_2272_, v_numParams_2273_, v_ctors_2298_, v___x_2301_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
lean_dec_ref_known(v___x_2302_, 1);
v___x_2303_ = lean_unsigned_to_nat(1u);
v___x_2304_ = lean_nat_add(v_start_2288_, v___x_2303_);
lean_dec(v_start_2288_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 1, v___x_2304_);
v___x_2306_ = v___x_2293_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_array_2287_);
lean_ctor_set(v_reuseFailAlloc_2310_, 1, v___x_2304_);
lean_ctor_set(v_reuseFailAlloc_2310_, 2, v_stop_2289_);
v___x_2306_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
size_t v___x_2307_; size_t v___x_2308_; 
v___x_2307_ = ((size_t)1ULL);
v___x_2308_ = lean_usize_add(v_i_2276_, v___x_2307_);
v_i_2276_ = v___x_2308_;
v_b_2277_ = v___x_2306_;
goto _start;
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
lean_del_object(v___x_2293_);
lean_dec(v_stop_2289_);
lean_dec(v_start_2288_);
lean_dec_ref(v_array_2287_);
lean_dec(v_numParams_2273_);
lean_dec_ref(v_infos_2272_);
v_a_2311_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2302_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2302_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2___boxed(lean_object* v_infos_2323_, lean_object* v_numParams_2324_, lean_object* v_as_2325_, lean_object* v_sz_2326_, lean_object* v_i_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2326_);
lean_dec(v_sz_2326_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2327_);
lean_dec(v_i_2327_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2323_, v_numParams_2324_, v_as_2325_, v_sz_boxed_2336_, v_i_boxed_2337_, v_b_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec_ref(v_as_2325_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(lean_object* v_numParams_2339_, lean_object* v_infos_2340_, lean_object* v_coinductiveElabData_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; size_t v_sz_2352_; size_t v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_array_get_size(v_coinductiveElabData_2341_);
v___x_2351_ = l_Array_toSubarray___redArg(v_coinductiveElabData_2341_, v___x_2349_, v___x_2350_);
v_sz_2352_ = lean_array_size(v_infos_2340_);
v___x_2353_ = ((size_t)0ULL);
lean_inc_ref(v_infos_2340_);
v___x_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__2(v_infos_2340_, v_numParams_2339_, v_infos_2340_, v_sz_2352_, v___x_2353_, v___x_2351_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec_ref(v_infos_2340_);
if (lean_obj_tag(v___x_2354_) == 0)
{
lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2362_; 
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v___x_2354_, 0);
lean_dec(v_unused_2363_);
v___x_2356_ = v___x_2354_;
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
else
{
lean_dec(v___x_2354_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_box(0);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 0, v___x_2358_);
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2354_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2354_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2354_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2354_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors___boxed(lean_object* v_numParams_2372_, lean_object* v_infos_2373_, lean_object* v_coinductiveElabData_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v_numParams_2372_, v_infos_2373_, v_coinductiveElabData_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec_ref(v_a_2377_);
lean_dec(v_a_2376_);
lean_dec_ref(v_a_2375_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(lean_object* v_a_2383_, lean_object* v_infos_2384_, lean_object* v_numParams_2385_, lean_object* v_as_2386_, lean_object* v_as_x27_2387_, lean_object* v_b_2388_, lean_object* v_a_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2383_, v_infos_2384_, v_numParams_2385_, v_as_x27_2387_, v_b_2388_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___boxed(lean_object* v_a_2398_, lean_object* v_infos_2399_, lean_object* v_numParams_2400_, lean_object* v_as_2401_, lean_object* v_as_x27_2402_, lean_object* v_b_2403_, lean_object* v_a_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1(v_a_2398_, v_infos_2399_, v_numParams_2400_, v_as_2401_, v_as_x27_2402_, v_b_2403_, v_a_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v_as_x27_2402_);
lean_dec(v_as_2401_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(lean_object* v_00_u03b1_2413_, lean_object* v_msg_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___redArg(v_msg_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2423_, lean_object* v_msg_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0(v_00_u03b1_2423_, v_msg_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(lean_object* v_msgData_2433_, lean_object* v_macroStack_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_msgData_2433_, v_macroStack_2434_, v___y_2439_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_2443_, lean_object* v_macroStack_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1(v_msgData_2443_, v_macroStack_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(lean_object* v_mvarId_2453_, lean_object* v_x_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_2453_, v_x_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
v_a_2469_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2460_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2460_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg___boxed(lean_object* v_mvarId_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2477_, v_x_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(lean_object* v_00_u03b1_2485_, lean_object* v_mvarId_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_mvarId_2486_, v_x_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_mvarId_2495_, lean_object* v_x_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4(v_00_u03b1_2494_, v_mvarId_2495_, v_x_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(lean_object* v_type_2503_, lean_object* v_maxFVars_x3f_2504_, lean_object* v_k_2505_, uint8_t v_cleanupAnnotations_2506_, uint8_t v_whnfType_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___f_2513_; lean_object* v___x_2514_; 
v___f_2513_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2513_, 0, v_k_2505_);
v___x_2514_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_2503_, v_maxFVars_x3f_2504_, v___f_2513_, v_cleanupAnnotations_2506_, v_whnfType_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
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
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_a_2523_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2514_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2514_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg___boxed(lean_object* v_type_2531_, lean_object* v_maxFVars_x3f_2532_, lean_object* v_k_2533_, lean_object* v_cleanupAnnotations_2534_, lean_object* v_whnfType_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2541_; uint8_t v_whnfType_boxed_2542_; lean_object* v_res_2543_; 
v_cleanupAnnotations_boxed_2541_ = lean_unbox(v_cleanupAnnotations_2534_);
v_whnfType_boxed_2542_ = lean_unbox(v_whnfType_2535_);
v_res_2543_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2531_, v_maxFVars_x3f_2532_, v_k_2533_, v_cleanupAnnotations_boxed_2541_, v_whnfType_boxed_2542_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(lean_object* v_00_u03b1_2544_, lean_object* v_type_2545_, lean_object* v_maxFVars_x3f_2546_, lean_object* v_k_2547_, uint8_t v_cleanupAnnotations_2548_, uint8_t v_whnfType_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_2545_, v_maxFVars_x3f_2546_, v_k_2547_, v_cleanupAnnotations_2548_, v_whnfType_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___boxed(lean_object* v_00_u03b1_2556_, lean_object* v_type_2557_, lean_object* v_maxFVars_x3f_2558_, lean_object* v_k_2559_, lean_object* v_cleanupAnnotations_2560_, lean_object* v_whnfType_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2567_; uint8_t v_whnfType_boxed_2568_; lean_object* v_res_2569_; 
v_cleanupAnnotations_boxed_2567_ = lean_unbox(v_cleanupAnnotations_2560_);
v_whnfType_boxed_2568_ = lean_unbox(v_whnfType_2561_);
v_res_2569_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5(v_00_u03b1_2556_, v_type_2557_, v_maxFVars_x3f_2558_, v_k_2559_, v_cleanupAnnotations_boxed_2567_, v_whnfType_boxed_2568_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(lean_object* v_ref_2570_, lean_object* v_msg_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_fileName_2577_; lean_object* v_fileMap_2578_; lean_object* v_options_2579_; lean_object* v_currRecDepth_2580_; lean_object* v_maxRecDepth_2581_; lean_object* v_ref_2582_; lean_object* v_currNamespace_2583_; lean_object* v_openDecls_2584_; lean_object* v_initHeartbeats_2585_; lean_object* v_maxHeartbeats_2586_; lean_object* v_quotContext_2587_; lean_object* v_currMacroScope_2588_; uint8_t v_diag_2589_; lean_object* v_cancelTk_x3f_2590_; uint8_t v_suppressElabErrors_2591_; lean_object* v_inheritedTraceOptions_2592_; lean_object* v_ref_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_fileName_2577_ = lean_ctor_get(v___y_2574_, 0);
v_fileMap_2578_ = lean_ctor_get(v___y_2574_, 1);
v_options_2579_ = lean_ctor_get(v___y_2574_, 2);
v_currRecDepth_2580_ = lean_ctor_get(v___y_2574_, 3);
v_maxRecDepth_2581_ = lean_ctor_get(v___y_2574_, 4);
v_ref_2582_ = lean_ctor_get(v___y_2574_, 5);
v_currNamespace_2583_ = lean_ctor_get(v___y_2574_, 6);
v_openDecls_2584_ = lean_ctor_get(v___y_2574_, 7);
v_initHeartbeats_2585_ = lean_ctor_get(v___y_2574_, 8);
v_maxHeartbeats_2586_ = lean_ctor_get(v___y_2574_, 9);
v_quotContext_2587_ = lean_ctor_get(v___y_2574_, 10);
v_currMacroScope_2588_ = lean_ctor_get(v___y_2574_, 11);
v_diag_2589_ = lean_ctor_get_uint8(v___y_2574_, sizeof(void*)*14);
v_cancelTk_x3f_2590_ = lean_ctor_get(v___y_2574_, 12);
v_suppressElabErrors_2591_ = lean_ctor_get_uint8(v___y_2574_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2592_ = lean_ctor_get(v___y_2574_, 13);
v_ref_2593_ = l_Lean_replaceRef(v_ref_2570_, v_ref_2582_);
lean_inc_ref(v_inheritedTraceOptions_2592_);
lean_inc(v_cancelTk_x3f_2590_);
lean_inc(v_currMacroScope_2588_);
lean_inc(v_quotContext_2587_);
lean_inc(v_maxHeartbeats_2586_);
lean_inc(v_initHeartbeats_2585_);
lean_inc(v_openDecls_2584_);
lean_inc(v_currNamespace_2583_);
lean_inc(v_maxRecDepth_2581_);
lean_inc(v_currRecDepth_2580_);
lean_inc_ref(v_options_2579_);
lean_inc_ref(v_fileMap_2578_);
lean_inc_ref(v_fileName_2577_);
v___x_2594_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2594_, 0, v_fileName_2577_);
lean_ctor_set(v___x_2594_, 1, v_fileMap_2578_);
lean_ctor_set(v___x_2594_, 2, v_options_2579_);
lean_ctor_set(v___x_2594_, 3, v_currRecDepth_2580_);
lean_ctor_set(v___x_2594_, 4, v_maxRecDepth_2581_);
lean_ctor_set(v___x_2594_, 5, v_ref_2593_);
lean_ctor_set(v___x_2594_, 6, v_currNamespace_2583_);
lean_ctor_set(v___x_2594_, 7, v_openDecls_2584_);
lean_ctor_set(v___x_2594_, 8, v_initHeartbeats_2585_);
lean_ctor_set(v___x_2594_, 9, v_maxHeartbeats_2586_);
lean_ctor_set(v___x_2594_, 10, v_quotContext_2587_);
lean_ctor_set(v___x_2594_, 11, v_currMacroScope_2588_);
lean_ctor_set(v___x_2594_, 12, v_cancelTk_x3f_2590_);
lean_ctor_set(v___x_2594_, 13, v_inheritedTraceOptions_2592_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*14, v_diag_2589_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*14 + 1, v_suppressElabErrors_2591_);
v___x_2595_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2571_, v___y_2572_, v___y_2573_, v___x_2594_, v___y_2575_);
lean_dec_ref_known(v___x_2594_, 14);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2596_, lean_object* v_msg_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2596_, v_msg_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v_ref_2596_);
return v_res_2603_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
return v___x_2606_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2608_ = lean_unsigned_to_nat(0u);
v___x_2609_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
lean_ctor_set(v___x_2609_, 2, v___x_2608_);
lean_ctor_set(v___x_2609_, 3, v___x_2608_);
lean_ctor_set(v___x_2609_, 4, v___x_2607_);
lean_ctor_set(v___x_2609_, 5, v___x_2607_);
lean_ctor_set(v___x_2609_, 6, v___x_2607_);
lean_ctor_set(v___x_2609_, 7, v___x_2607_);
lean_ctor_set(v___x_2609_, 8, v___x_2607_);
lean_ctor_set(v___x_2609_, 9, v___x_2607_);
lean_ctor_set(v___x_2609_, 10, v___x_2607_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_unsigned_to_nat(32u);
v___x_2611_ = lean_mk_empty_array_with_capacity(v___x_2610_);
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2613_ = ((size_t)5ULL);
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = lean_unsigned_to_nat(32u);
v___x_2616_ = lean_mk_empty_array_with_capacity(v___x_2615_);
v___x_2617_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2618_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
lean_ctor_set(v___x_2618_, 1, v___x_2616_);
lean_ctor_set(v___x_2618_, 2, v___x_2614_);
lean_ctor_set(v___x_2618_, 3, v___x_2614_);
lean_ctor_set_usize(v___x_2618_, 4, v___x_2613_);
return v___x_2618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2619_ = lean_box(1);
v___x_2620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___x_2620_);
lean_ctor_set(v___x_2622_, 2, v___x_2619_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2625_ = l_Lean_stringToMessageData(v___x_2624_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2628_ = l_Lean_stringToMessageData(v___x_2627_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2630_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2631_ = l_Lean_stringToMessageData(v___x_2630_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2633_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2634_ = l_Lean_stringToMessageData(v___x_2633_);
return v___x_2634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2637_ = l_Lean_stringToMessageData(v___x_2636_);
return v___x_2637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2640_ = l_Lean_stringToMessageData(v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2644_, lean_object* v_declHint_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; lean_object* v_env_2649_; uint8_t v___x_2650_; 
v___x_2648_ = lean_st_ref_get(v___y_2646_);
v_env_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc_ref(v_env_2649_);
lean_dec(v___x_2648_);
v___x_2650_ = l_Lean_Name_isAnonymous(v_declHint_2645_);
if (v___x_2650_ == 0)
{
uint8_t v_isExporting_2651_; 
v_isExporting_2651_ = lean_ctor_get_uint8(v_env_2649_, sizeof(void*)*8);
if (v_isExporting_2651_ == 0)
{
lean_object* v___x_2652_; 
lean_dec_ref(v_env_2649_);
lean_dec(v_declHint_2645_);
v___x_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2652_, 0, v_msg_2644_);
return v___x_2652_;
}
else
{
lean_object* v___x_2653_; uint8_t v___x_2654_; 
lean_inc_ref(v_env_2649_);
v___x_2653_ = l_Lean_Environment_setExporting(v_env_2649_, v___x_2650_);
lean_inc(v_declHint_2645_);
lean_inc_ref(v___x_2653_);
v___x_2654_ = l_Lean_Environment_contains(v___x_2653_, v_declHint_2645_, v_isExporting_2651_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref(v___x_2653_);
lean_dec_ref(v_env_2649_);
lean_dec(v_declHint_2645_);
v___x_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2655_, 0, v_msg_2644_);
return v___x_2655_;
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v_c_2661_; lean_object* v___x_2662_; 
v___x_2656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2);
v___x_2657_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5);
v___x_2658_ = l_Lean_Options_empty;
v___x_2659_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2653_);
lean_ctor_set(v___x_2659_, 1, v___x_2656_);
lean_ctor_set(v___x_2659_, 2, v___x_2657_);
lean_ctor_set(v___x_2659_, 3, v___x_2658_);
lean_inc(v_declHint_2645_);
v___x_2660_ = l_Lean_MessageData_ofConstName(v_declHint_2645_, v___x_2650_);
v_c_2661_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2661_, 0, v___x_2659_);
lean_ctor_set(v_c_2661_, 1, v___x_2660_);
v___x_2662_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2649_, v_declHint_2645_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec_ref(v_env_2649_);
lean_dec(v_declHint_2645_);
v___x_2663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
lean_ctor_set(v___x_2664_, 1, v_c_2661_);
v___x_2665_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_MessageData_note(v___x_2666_);
v___x_2668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2668_, 0, v_msg_2644_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
return v___x_2669_;
}
else
{
lean_object* v_val_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2705_; 
v_val_2670_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2705_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2705_ == 0)
{
v___x_2672_ = v___x_2662_;
v_isShared_2673_ = v_isSharedCheck_2705_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_val_2670_);
lean_dec(v___x_2662_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2705_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v_mod_2677_; uint8_t v___x_2678_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = l_Lean_Environment_header(v_env_2649_);
lean_dec_ref(v_env_2649_);
v___x_2676_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2675_);
v_mod_2677_ = lean_array_get(v___x_2674_, v___x_2676_, v_val_2670_);
lean_dec(v_val_2670_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = l_Lean_isPrivateName(v_declHint_2645_);
lean_dec(v_declHint_2645_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11);
v___x_2680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2679_);
lean_ctor_set(v___x_2680_, 1, v_c_2661_);
v___x_2681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13);
v___x_2682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2680_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_MessageData_ofName(v_mod_2677_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15);
v___x_2686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2684_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_MessageData_note(v___x_2686_);
v___x_2688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_msg_2644_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2688_);
v___x_2690_ = v___x_2672_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7);
v___x_2693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
lean_ctor_set(v___x_2693_, 1, v_c_2661_);
v___x_2694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17);
v___x_2695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2693_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l_Lean_MessageData_ofName(v_mod_2677_);
v___x_2697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2695_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v___x_2698_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19);
v___x_2699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = l_Lean_MessageData_note(v___x_2699_);
v___x_2701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_msg_2644_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 0);
lean_ctor_set(v___x_2672_, 0, v___x_2701_);
v___x_2703_ = v___x_2672_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
return v___x_2703_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2706_; 
lean_dec_ref(v_env_2649_);
lean_dec(v_declHint_2645_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v_msg_2644_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2707_, lean_object* v_declHint_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2707_, v_declHint_2708_, v___y_2709_);
lean_dec(v___y_2709_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2712_, lean_object* v_declHint_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2729_; 
v___x_2719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2712_, v_declHint_2713_, v___y_2717_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2729_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2729_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2724_ = l_Lean_unknownIdentifierMessageTag;
v___x_2725_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2724_);
lean_ctor_set(v___x_2725_, 1, v_a_2720_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 0, v___x_2725_);
v___x_2727_ = v___x_2722_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2730_, lean_object* v_declHint_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2730_, v_declHint_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2738_, lean_object* v_msg_2739_, lean_object* v_declHint_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v___x_2746_; lean_object* v_a_2747_; lean_object* v___x_2748_; 
v___x_2746_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2739_, v_declHint_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v___x_2748_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2738_, v_a_2747_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2749_, lean_object* v_msg_2750_, lean_object* v_declHint_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2749_, v_msg_2750_, v_declHint_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v_ref_2749_);
return v_res_2757_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2761_, lean_object* v_constName_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v___x_2768_; uint8_t v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2768_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2769_ = 0;
lean_inc(v_constName_2762_);
v___x_2770_ = l_Lean_MessageData_ofConstName(v_constName_2762_, v___x_2769_);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2768_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2771_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2761_, v___x_2773_, v_constName_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2775_, lean_object* v_constName_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2775_, v_constName_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v_ref_2775_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_ref_2789_; lean_object* v___x_2790_; 
v_ref_2789_ = lean_ctor_get(v___y_2786_, 5);
v___x_2790_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2789_, v_constName_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2804_; lean_object* v_env_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; 
v___x_2804_ = lean_st_ref_get(v___y_2802_);
v_env_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc_ref(v_env_2805_);
lean_dec(v___x_2804_);
v___x_2806_ = 0;
lean_inc(v_constName_2798_);
v___x_2807_ = l_Lean_Environment_find_x3f(v_env_2805_, v_constName_2798_, v___x_2806_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2798_, v___y_2799_, v___y_2800_, v___y_2801_, v___y_2802_);
return v___x_2808_;
}
else
{
lean_object* v_val_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_constName_2798_);
v_val_2809_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2807_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_val_2809_);
lean_dec(v___x_2807_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
lean_ctor_set_tag(v___x_2811_, 0);
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_val_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2823_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2824_, lean_object* v_as_2825_, size_t v_i_2826_, size_t v_stop_2827_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_usize_dec_eq(v_i_2826_, v_stop_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; uint8_t v___x_2830_; 
v___x_2829_ = lean_array_uget_borrowed(v_as_2825_, v_i_2826_);
v___x_2830_ = l_Lean_Expr_isAppOf(v_e_2824_, v___x_2829_);
if (v___x_2830_ == 0)
{
size_t v___x_2831_; size_t v___x_2832_; 
v___x_2831_ = ((size_t)1ULL);
v___x_2832_ = lean_usize_add(v_i_2826_, v___x_2831_);
v_i_2826_ = v___x_2832_;
goto _start;
}
else
{
return v___x_2830_;
}
}
else
{
uint8_t v___x_2834_; 
v___x_2834_ = 0;
return v___x_2834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2835_, lean_object* v_as_2836_, lean_object* v_i_2837_, lean_object* v_stop_2838_){
_start:
{
size_t v_i_boxed_2839_; size_t v_stop_boxed_2840_; uint8_t v_res_2841_; lean_object* v_r_2842_; 
v_i_boxed_2839_ = lean_unbox_usize(v_i_2837_);
lean_dec(v_i_2837_);
v_stop_boxed_2840_ = lean_unbox_usize(v_stop_2838_);
lean_dec(v_stop_2838_);
v_res_2841_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2835_, v_as_2836_, v_i_boxed_2839_, v_stop_boxed_2840_);
lean_dec_ref(v_as_2836_);
lean_dec_ref(v_e_2835_);
v_r_2842_ = lean_box(v_res_2841_);
return v_r_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2843_, lean_object* v_name_2844_, lean_object* v_levels_2845_, lean_object* v_params_2846_, lean_object* v___y_2847_, lean_object* v___x_2848_, lean_object* v_e_2849_){
_start:
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Lean_Expr_isApp(v_e_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; 
lean_dec_ref(v_e_2849_);
lean_dec_ref(v_params_2846_);
lean_dec(v_levels_2845_);
lean_dec(v_name_2844_);
lean_dec(v_numParams_2843_);
v___x_2851_ = lean_box(0);
return v___x_2851_;
}
else
{
lean_object* v_dummy_2852_; lean_object* v_nargs_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; uint8_t v___y_2861_; uint8_t v___x_2871_; 
v_dummy_2852_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2853_ = l_Lean_Expr_getAppNumArgs(v_e_2849_);
lean_inc(v_nargs_2853_);
v___x_2854_ = lean_mk_array(v_nargs_2853_, v_dummy_2852_);
v___x_2855_ = lean_unsigned_to_nat(1u);
v___x_2856_ = lean_nat_sub(v_nargs_2853_, v___x_2855_);
lean_dec(v_nargs_2853_);
lean_inc_ref(v_e_2849_);
v___x_2857_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2849_, v___x_2854_, v___x_2856_);
v___x_2858_ = lean_array_get_size(v___x_2857_);
v___x_2859_ = l_Array_toSubarray___redArg(v___x_2857_, v_numParams_2843_, v___x_2858_);
v___x_2871_ = l_Lean_Expr_isAppOf(v_e_2849_, v_name_2844_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; uint8_t v___x_2873_; 
lean_dec(v_name_2844_);
v___x_2872_ = lean_array_get_size(v___y_2847_);
v___x_2873_ = lean_nat_dec_lt(v___x_2848_, v___x_2872_);
if (v___x_2873_ == 0)
{
v___y_2861_ = v___x_2871_;
goto v___jp_2860_;
}
else
{
if (v___x_2873_ == 0)
{
v___y_2861_ = v___x_2871_;
goto v___jp_2860_;
}
else
{
size_t v___x_2874_; size_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2874_ = ((size_t)0ULL);
v___x_2875_ = lean_usize_of_nat(v___x_2872_);
v___x_2876_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2849_, v___y_2847_, v___x_2874_, v___x_2875_);
v___y_2861_ = v___x_2876_;
goto v___jp_2860_;
}
}
}
else
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
lean_dec_ref(v_e_2849_);
v___x_2877_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2844_);
v___x_2878_ = l_Lean_mkConst(v___x_2877_, v_levels_2845_);
v___x_2879_ = l_Subarray_copy___redArg(v___x_2859_);
v___x_2880_ = l_Array_append___redArg(v_params_2846_, v___x_2879_);
lean_dec_ref(v___x_2879_);
v___x_2881_ = l_Lean_mkAppN(v___x_2878_, v___x_2880_);
lean_dec_ref(v___x_2880_);
v___x_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2881_);
return v___x_2882_;
}
v___jp_2860_:
{
if (v___y_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec_ref(v___x_2859_);
lean_dec_ref(v_e_2849_);
lean_dec_ref(v_params_2846_);
lean_dec(v_levels_2845_);
v___x_2862_ = lean_box(0);
return v___x_2862_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2863_ = l_Lean_Expr_getAppFn(v_e_2849_);
lean_dec_ref(v_e_2849_);
v___x_2864_ = l_Lean_Expr_constName(v___x_2863_);
lean_dec_ref(v___x_2863_);
v___x_2865_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2864_);
v___x_2866_ = l_Lean_mkConst(v___x_2865_, v_levels_2845_);
v___x_2867_ = l_Subarray_copy___redArg(v___x_2859_);
v___x_2868_ = l_Array_append___redArg(v_params_2846_, v___x_2867_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2883_, lean_object* v_name_2884_, lean_object* v_levels_2885_, lean_object* v_params_2886_, lean_object* v___y_2887_, lean_object* v___x_2888_, lean_object* v_e_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2883_, v_name_2884_, v_levels_2885_, v_params_2886_, v___y_2887_, v___x_2888_, v_e_2889_);
lean_dec(v___x_2888_);
lean_dec_ref(v___y_2887_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v_eqProof_2891_, lean_object* v___x_2892_, lean_object* v_eNew_2893_, lean_object* v_snd_2894_, lean_object* v___x_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lean_Meta_mkEqMP(v_eqProof_2891_, v___x_2892_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_eNew_2893_);
v___x_2904_ = lean_box(0);
v___x_2905_ = l_Lean_MVarId_replace(v_snd_2894_, v___x_2895_, v_a_2902_, v___x_2903_, v___x_2904_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
return v___x_2905_;
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v___x_2895_);
lean_dec(v_snd_2894_);
lean_dec_ref(v_eNew_2893_);
v_a_2906_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2901_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2901_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object* v_eqProof_2914_, lean_object* v___x_2915_, lean_object* v_eNew_2916_, lean_object* v_snd_2917_, lean_object* v___x_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_res_2924_; 
v_res_2924_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_2914_, v___x_2915_, v_eNew_2916_, v_snd_2917_, v___x_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
return v_res_2924_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0));
v___x_2927_ = l_Lean_stringToMessageData(v___x_2926_);
return v___x_2927_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_2951_, lean_object* v___x_2952_, uint8_t v___x_2953_, lean_object* v___x_2954_, lean_object* v___x_2955_, uint8_t v___x_2956_, lean_object* v___x_2957_, lean_object* v_params_2958_, lean_object* v_args_2959_, lean_object* v_indices_2960_, uint8_t v___x_2961_, lean_object* v___x_2962_, lean_object* v_a_2963_, lean_object* v___x_2964_, lean_object* v___f_2965_, lean_object* v___x_2966_, lean_object* v_targetArgs_2967_, lean_object* v_x_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___x_2974_; uint8_t v___x_2975_; 
v___x_2974_ = lean_array_get_size(v_targetArgs_2967_);
v___x_2975_ = lean_nat_dec_eq(v___x_2974_, v___x_2951_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v___x_2952_);
v___x_2976_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_2977_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_2976_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
return v___x_2977_;
}
else
{
lean_object* v___x_2978_; 
lean_inc(v___y_2972_);
lean_inc_ref(v___y_2971_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc_ref(v___x_2952_);
v___x_2978_ = lean_infer_type(v___x_2952_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
if (lean_obj_tag(v_a_2979_) == 7)
{
lean_object* v_binderType_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_binderType_2980_ = lean_ctor_get(v_a_2979_, 1);
lean_inc_ref(v_binderType_2980_);
lean_dec_ref_known(v_a_2979_, 3);
v___x_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2981_, 0, v_binderType_2980_);
v___x_2982_ = l_Lean_Meta_mkFreshExprMVar(v___x_2981_, v___x_2953_, v___x_2954_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = l_Lean_Expr_mvarId_x21(v_a_2983_);
v___x_2985_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2984_, v___x_2955_, v___x_2956_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = lean_array_fget_borrowed(v_targetArgs_2967_, v___x_2957_);
lean_inc(v___x_2987_);
v___x_2988_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2986_, v___x_2987_, v___y_2970_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3070_; 
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3070_ == 0)
{
lean_object* v_unused_3071_; 
v_unused_3071_ = lean_ctor_get(v___x_2988_, 0);
lean_dec(v_unused_3071_);
v___x_2990_ = v___x_2988_;
v_isShared_2991_ = v_isSharedCheck_3070_;
goto v_resetjp_2989_;
}
else
{
lean_dec(v___x_2988_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3070_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; lean_object* v___x_2997_; 
v___x_2992_ = l_Lean_Expr_app___override(v___x_2952_, v_a_2983_);
lean_inc_ref(v_params_2958_);
v___x_2993_ = l_Array_append___redArg(v_params_2958_, v_args_2959_);
v___x_2994_ = l_Array_append___redArg(v___x_2993_, v_indices_2960_);
v___x_2995_ = l_Array_append___redArg(v___x_2994_, v_targetArgs_2967_);
v___x_2996_ = 1;
v___x_2997_ = l_Lean_Meta_mkLambdaFVars(v___x_2995_, v___x_2992_, v___x_2961_, v___x_2956_, v___x_2961_, v___x_2956_, v___x_2996_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec_ref(v___x_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_2998_, v___y_2970_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref_known(v___x_2999_, 1);
v___x_3001_ = l_Lean_Meta_mkForallFVars(v_params_2958_, v___x_2962_, v___x_2961_, v___x_2956_, v___x_2956_, v___x_2996_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec_ref(v_params_2958_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = l_Lean_ConstantInfo_levelParams(v_a_2963_);
v___x_3004_ = l_Lean_mkCasesOnName(v___x_2964_);
v___x_3005_ = lean_box(0);
lean_inc(v___x_3004_);
v___x_3006_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_3004_, v___x_3003_, v_a_3002_, v_a_3000_, v___x_3005_, v___y_2972_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
if (v_isShared_2991_ == 0)
{
lean_ctor_set_tag(v___x_2990_, 1);
lean_ctor_set(v___x_2990_, 0, v_a_3007_);
v___x_3009_ = v___x_2990_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3007_);
v___x_3009_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Lean_addDecl(v___x_3009_, v___x_2961_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec_ref_known(v___x_3010_, 1);
v___x_3011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8));
v___x_3012_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3012_, 0, v___x_3004_);
lean_closure_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_box(0);
v___x_3015_ = lean_box(1);
v___x_3016_ = lean_mk_empty_array_with_capacity(v___x_2957_);
v___x_3017_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3017_, 0, v___x_3013_);
lean_ctor_set(v___x_3017_, 1, v___x_3014_);
lean_ctor_set(v___x_3017_, 2, v___x_3013_);
lean_ctor_set(v___x_3017_, 3, v___f_2965_);
lean_ctor_set(v___x_3017_, 4, v___x_3015_);
lean_ctor_set(v___x_3017_, 5, v___x_3015_);
lean_ctor_set(v___x_3017_, 6, v___x_3013_);
lean_ctor_set(v___x_3017_, 7, v___x_3016_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8, v___x_2956_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 1, v___x_2956_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 2, v___x_2956_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 3, v___x_2956_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 4, v___x_2961_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 5, v___x_2961_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 6, v___x_2961_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 7, v___x_2961_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 8, v___x_2956_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 9, v___x_2961_);
lean_ctor_set_uint8(v___x_3017_, sizeof(void*)*8 + 10, v___x_2956_);
v___x_3018_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3018_, 0, v___x_2966_);
lean_ctor_set(v___x_3018_, 1, v___x_3015_);
lean_ctor_set(v___x_3018_, 2, v___x_3014_);
lean_ctor_set(v___x_3018_, 3, v___x_3014_);
lean_ctor_set(v___x_3018_, 4, v___x_3014_);
lean_ctor_set(v___x_3018_, 5, v___x_3015_);
lean_ctor_set(v___x_3018_, 6, v___x_3014_);
v___x_3019_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3012_, v___x_3017_, v___x_3018_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3028_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3022_ = v___x_3019_;
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v_fst_3024_; lean_object* v___x_3026_; 
v_fst_3024_ = lean_ctor_get(v_a_3020_, 0);
lean_inc(v_fst_3024_);
lean_dec(v_a_3020_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 0, v_fst_3024_);
v___x_3026_ = v___x_3022_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_fst_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
v_a_3029_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3019_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3019_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_dec(v___x_3004_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
return v___x_3010_;
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec(v___x_3004_);
lean_del_object(v___x_2990_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
v_a_3038_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3006_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3006_);
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
lean_dec(v_a_3000_);
lean_del_object(v___x_2990_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
v_a_3046_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3001_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3001_);
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
lean_del_object(v___x_2990_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
v_a_3054_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_2999_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_2999_);
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
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_del_object(v___x_2990_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
v_a_3062_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_2997_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_2997_);
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
}
else
{
lean_dec(v_a_2983_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2952_);
return v___x_2988_;
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec(v_a_2983_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2952_);
v_a_3072_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_2985_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_2985_);
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
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec_ref(v___x_2952_);
v_a_3080_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_2982_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_2982_);
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
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec(v_a_2979_);
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v___x_2952_);
v___x_3088_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3089_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3088_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
return v___x_3089_;
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec(v___x_2966_);
lean_dec_ref(v___f_2965_);
lean_dec(v___x_2964_);
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_params_2958_);
lean_dec_ref(v___x_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v___x_2952_);
v_a_3090_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_2978_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_2978_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3098_ = _args[0];
lean_object* v___x_3099_ = _args[1];
lean_object* v___x_3100_ = _args[2];
lean_object* v___x_3101_ = _args[3];
lean_object* v___x_3102_ = _args[4];
lean_object* v___x_3103_ = _args[5];
lean_object* v___x_3104_ = _args[6];
lean_object* v_params_3105_ = _args[7];
lean_object* v_args_3106_ = _args[8];
lean_object* v_indices_3107_ = _args[9];
lean_object* v___x_3108_ = _args[10];
lean_object* v___x_3109_ = _args[11];
lean_object* v_a_3110_ = _args[12];
lean_object* v___x_3111_ = _args[13];
lean_object* v___f_3112_ = _args[14];
lean_object* v___x_3113_ = _args[15];
lean_object* v_targetArgs_3114_ = _args[16];
lean_object* v_x_3115_ = _args[17];
lean_object* v___y_3116_ = _args[18];
lean_object* v___y_3117_ = _args[19];
lean_object* v___y_3118_ = _args[20];
lean_object* v___y_3119_ = _args[21];
lean_object* v___y_3120_ = _args[22];
_start:
{
uint8_t v___x_16841__boxed_3121_; uint8_t v___x_16844__boxed_3122_; uint8_t v___x_16846__boxed_3123_; lean_object* v_res_3124_; 
v___x_16841__boxed_3121_ = lean_unbox(v___x_3100_);
v___x_16844__boxed_3122_ = lean_unbox(v___x_3103_);
v___x_16846__boxed_3123_ = lean_unbox(v___x_3108_);
v_res_3124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3098_, v___x_3099_, v___x_16841__boxed_3121_, v___x_3101_, v___x_3102_, v___x_16844__boxed_3122_, v___x_3104_, v_params_3105_, v_args_3106_, v_indices_3107_, v___x_16846__boxed_3123_, v___x_3109_, v_a_3110_, v___x_3111_, v___f_3112_, v___x_3113_, v_targetArgs_3114_, v_x_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec_ref(v_x_3115_);
lean_dec_ref(v_targetArgs_3114_);
lean_dec_ref(v_a_3110_);
lean_dec_ref(v_indices_3107_);
lean_dec_ref(v_args_3106_);
lean_dec(v___x_3104_);
lean_dec(v___x_3098_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3125_, lean_object* v___x_3126_, uint8_t v___x_3127_, lean_object* v___x_3128_, lean_object* v___x_3129_, uint8_t v___x_3130_, lean_object* v___x_3131_, lean_object* v_params_3132_, lean_object* v_args_3133_, uint8_t v___x_3134_, lean_object* v___x_3135_, lean_object* v_a_3136_, lean_object* v___x_3137_, lean_object* v___f_3138_, lean_object* v___x_3139_, lean_object* v___x_3140_, lean_object* v_indices_3141_, lean_object* v_goalType_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; 
v___x_3148_ = l_Lean_mkAppN(v___x_3125_, v_indices_3141_);
v___x_3149_ = lean_box(v___x_3127_);
v___x_3150_ = lean_box(v___x_3130_);
v___x_3151_ = lean_box(v___x_3134_);
v___f_3152_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 23, 16);
lean_closure_set(v___f_3152_, 0, v___x_3126_);
lean_closure_set(v___f_3152_, 1, v___x_3148_);
lean_closure_set(v___f_3152_, 2, v___x_3149_);
lean_closure_set(v___f_3152_, 3, v___x_3128_);
lean_closure_set(v___f_3152_, 4, v___x_3129_);
lean_closure_set(v___f_3152_, 5, v___x_3150_);
lean_closure_set(v___f_3152_, 6, v___x_3131_);
lean_closure_set(v___f_3152_, 7, v_params_3132_);
lean_closure_set(v___f_3152_, 8, v_args_3133_);
lean_closure_set(v___f_3152_, 9, v_indices_3141_);
lean_closure_set(v___f_3152_, 10, v___x_3151_);
lean_closure_set(v___f_3152_, 11, v___x_3135_);
lean_closure_set(v___f_3152_, 12, v_a_3136_);
lean_closure_set(v___f_3152_, 13, v___x_3137_);
lean_closure_set(v___f_3152_, 14, v___f_3138_);
lean_closure_set(v___f_3152_, 15, v___x_3139_);
v___x_3153_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3142_, v___x_3140_, v___f_3152_, v___x_3134_, v___x_3134_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3154_ = _args[0];
lean_object* v___x_3155_ = _args[1];
lean_object* v___x_3156_ = _args[2];
lean_object* v___x_3157_ = _args[3];
lean_object* v___x_3158_ = _args[4];
lean_object* v___x_3159_ = _args[5];
lean_object* v___x_3160_ = _args[6];
lean_object* v_params_3161_ = _args[7];
lean_object* v_args_3162_ = _args[8];
lean_object* v___x_3163_ = _args[9];
lean_object* v___x_3164_ = _args[10];
lean_object* v_a_3165_ = _args[11];
lean_object* v___x_3166_ = _args[12];
lean_object* v___f_3167_ = _args[13];
lean_object* v___x_3168_ = _args[14];
lean_object* v___x_3169_ = _args[15];
lean_object* v_indices_3170_ = _args[16];
lean_object* v_goalType_3171_ = _args[17];
lean_object* v___y_3172_ = _args[18];
lean_object* v___y_3173_ = _args[19];
lean_object* v___y_3174_ = _args[20];
lean_object* v___y_3175_ = _args[21];
lean_object* v___y_3176_ = _args[22];
_start:
{
uint8_t v___x_17177__boxed_3177_; uint8_t v___x_17180__boxed_3178_; uint8_t v___x_17182__boxed_3179_; lean_object* v_res_3180_; 
v___x_17177__boxed_3177_ = lean_unbox(v___x_3156_);
v___x_17180__boxed_3178_ = lean_unbox(v___x_3159_);
v___x_17182__boxed_3179_ = lean_unbox(v___x_3163_);
v_res_3180_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3154_, v___x_3155_, v___x_17177__boxed_3177_, v___x_3157_, v___x_3158_, v___x_17180__boxed_3178_, v___x_3160_, v_params_3161_, v_args_3162_, v___x_17182__boxed_3179_, v___x_3164_, v_a_3165_, v___x_3166_, v___f_3167_, v___x_3168_, v___x_3169_, v_indices_3170_, v_goalType_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object* v___x_3181_, uint8_t v___x_3182_, lean_object* v_snd_3183_, lean_object* v___x_3184_, uint8_t v___x_3185_, lean_object* v___x_3186_, lean_object* v___x_3187_, lean_object* v_a_3188_, lean_object* v___x_3189_, uint8_t v___x_3190_, lean_object* v___x_3191_, lean_object* v___x_3192_, lean_object* v_params_3193_, lean_object* v_args_3194_, lean_object* v___x_3195_, lean_object* v_a_3196_, lean_object* v___x_3197_, lean_object* v___f_3198_, lean_object* v___x_3199_, lean_object* v___x_3200_, lean_object* v_numIndices_3201_, lean_object* v_goalType_3202_, lean_object* v___x_3203_, lean_object* v___x_3204_, lean_object* v_fst_3205_, lean_object* v___x_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
lean_object* v_lctx_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v_lctx_3212_ = lean_ctor_get(v___y_3207_, 2);
lean_inc(v___x_3181_);
lean_inc_ref(v_lctx_3212_);
v___x_3213_ = l_Lean_LocalContext_get_x21(v_lctx_3212_, v___x_3181_);
v___x_3214_ = l_Lean_LocalDecl_type(v___x_3213_);
lean_dec_ref(v___x_3213_);
v___x_3215_ = 2;
v___x_3216_ = lean_box(0);
v___x_3217_ = 0;
v___x_3218_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3218_, 0, v___x_3216_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1, v___x_3215_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1 + 1, v___x_3182_);
lean_ctor_set_uint8(v___x_3218_, sizeof(void*)*1 + 2, v___x_3217_);
lean_inc_ref(v___x_3184_);
lean_inc(v_snd_3183_);
v___x_3219_ = l_Lean_MVarId_rewrite(v_snd_3183_, v___x_3214_, v___x_3184_, v___x_3182_, v___x_3218_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v_eNew_3221_; lean_object* v_eqProof_3222_; lean_object* v___x_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
lean_dec_ref_known(v___x_3219_, 1);
v_eNew_3221_ = lean_ctor_get(v_a_3220_, 0);
lean_inc_ref(v_eNew_3221_);
v_eqProof_3222_ = lean_ctor_get(v_a_3220_, 1);
lean_inc_ref(v_eqProof_3222_);
lean_dec(v_a_3220_);
lean_inc(v___x_3181_);
v___x_3223_ = l_Lean_mkFVar(v___x_3181_);
lean_inc(v_snd_3183_);
v___f_3224_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3224_, 0, v_eqProof_3222_);
lean_closure_set(v___f_3224_, 1, v___x_3223_);
lean_closure_set(v___f_3224_, 2, v_eNew_3221_);
lean_closure_set(v___f_3224_, 3, v_snd_3183_);
lean_closure_set(v___f_3224_, 4, v___x_3181_);
v___x_3225_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3183_, v___f_3224_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___y_3228_; uint8_t v___x_3256_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3256_ = lean_nat_dec_lt(v___x_3203_, v___x_3204_);
if (v___x_3256_ == 0)
{
v___y_3228_ = v_fst_3205_;
goto v___jp_3227_;
}
else
{
lean_object* v_fvarId_3257_; lean_object* v_xs_x27_3258_; lean_object* v___x_3259_; 
v_fvarId_3257_ = lean_ctor_get(v_a_3226_, 0);
v_xs_x27_3258_ = lean_array_fset(v_fst_3205_, v___x_3203_, v___x_3206_);
lean_inc(v_fvarId_3257_);
v___x_3259_ = lean_array_fset(v_xs_x27_3258_, v___x_3203_, v_fvarId_3257_);
v___y_3228_ = v___x_3259_;
goto v___jp_3227_;
}
v___jp_3227_:
{
lean_object* v_mvarId_3229_; lean_object* v___x_3230_; 
v_mvarId_3229_ = lean_ctor_get(v_a_3226_, 1);
lean_inc(v_mvarId_3229_);
lean_dec(v_a_3226_);
v___x_3230_ = l_Lean_MVarId_revert(v_mvarId_3229_, v___y_3228_, v___x_3185_, v___x_3185_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v_snd_3232_; lean_object* v___x_3233_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v_snd_3232_ = lean_ctor_get(v_a_3231_, 1);
lean_inc(v_snd_3232_);
lean_dec(v_a_3231_);
v___x_3233_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3232_, v___x_3186_, v___y_3208_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3246_; 
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v___x_3233_, 0);
lean_dec(v_unused_3247_);
v___x_3235_ = v___x_3233_;
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
else
{
lean_dec(v___x_3233_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3246_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___f_3241_; lean_object* v___x_3243_; 
v___x_3237_ = l_Lean_Expr_app___override(v___x_3187_, v_a_3188_);
v___x_3238_ = lean_box(v___x_3190_);
v___x_3239_ = lean_box(v___x_3182_);
v___x_3240_ = lean_box(v___x_3185_);
v___f_3241_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 23, 16);
lean_closure_set(v___f_3241_, 0, v___x_3237_);
lean_closure_set(v___f_3241_, 1, v___x_3189_);
lean_closure_set(v___f_3241_, 2, v___x_3238_);
lean_closure_set(v___f_3241_, 3, v___x_3191_);
lean_closure_set(v___f_3241_, 4, v___x_3184_);
lean_closure_set(v___f_3241_, 5, v___x_3239_);
lean_closure_set(v___f_3241_, 6, v___x_3192_);
lean_closure_set(v___f_3241_, 7, v_params_3193_);
lean_closure_set(v___f_3241_, 8, v_args_3194_);
lean_closure_set(v___f_3241_, 9, v___x_3240_);
lean_closure_set(v___f_3241_, 10, v___x_3195_);
lean_closure_set(v___f_3241_, 11, v_a_3196_);
lean_closure_set(v___f_3241_, 12, v___x_3197_);
lean_closure_set(v___f_3241_, 13, v___f_3198_);
lean_closure_set(v___f_3241_, 14, v___x_3199_);
lean_closure_set(v___f_3241_, 15, v___x_3200_);
if (v_isShared_3236_ == 0)
{
lean_ctor_set_tag(v___x_3235_, 1);
lean_ctor_set(v___x_3235_, 0, v_numIndices_3201_);
v___x_3243_ = v___x_3235_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_numIndices_3201_);
v___x_3243_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; 
v___x_3244_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3202_, v___x_3243_, v___f_3241_, v___x_3185_, v___x_3185_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec_ref(v___y_3207_);
return v___x_3244_;
}
}
}
else
{
lean_dec_ref(v___y_3207_);
lean_dec_ref(v_goalType_3202_);
lean_dec(v_numIndices_3201_);
lean_dec(v___x_3200_);
lean_dec(v___x_3199_);
lean_dec_ref(v___f_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_a_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_args_3194_);
lean_dec_ref(v_params_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec(v___x_3189_);
lean_dec_ref(v_a_3188_);
lean_dec_ref(v___x_3187_);
lean_dec_ref(v___x_3184_);
return v___x_3233_;
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v___y_3207_);
lean_dec_ref(v_goalType_3202_);
lean_dec(v_numIndices_3201_);
lean_dec(v___x_3200_);
lean_dec(v___x_3199_);
lean_dec_ref(v___f_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_a_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_args_3194_);
lean_dec_ref(v_params_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec(v___x_3189_);
lean_dec_ref(v_a_3188_);
lean_dec_ref(v___x_3187_);
lean_dec_ref(v___x_3186_);
lean_dec_ref(v___x_3184_);
v_a_3248_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3230_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3230_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v___y_3207_);
lean_dec_ref(v_fst_3205_);
lean_dec_ref(v_goalType_3202_);
lean_dec(v_numIndices_3201_);
lean_dec(v___x_3200_);
lean_dec(v___x_3199_);
lean_dec_ref(v___f_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_a_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_args_3194_);
lean_dec_ref(v_params_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec(v___x_3189_);
lean_dec_ref(v_a_3188_);
lean_dec_ref(v___x_3187_);
lean_dec_ref(v___x_3186_);
lean_dec_ref(v___x_3184_);
v_a_3260_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3225_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3225_);
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
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec_ref(v___y_3207_);
lean_dec_ref(v_fst_3205_);
lean_dec_ref(v_goalType_3202_);
lean_dec(v_numIndices_3201_);
lean_dec(v___x_3200_);
lean_dec(v___x_3199_);
lean_dec_ref(v___f_3198_);
lean_dec(v___x_3197_);
lean_dec_ref(v_a_3196_);
lean_dec_ref(v___x_3195_);
lean_dec_ref(v_args_3194_);
lean_dec_ref(v_params_3193_);
lean_dec(v___x_3192_);
lean_dec(v___x_3191_);
lean_dec(v___x_3189_);
lean_dec_ref(v_a_3188_);
lean_dec_ref(v___x_3187_);
lean_dec_ref(v___x_3186_);
lean_dec_ref(v___x_3184_);
lean_dec(v_snd_3183_);
lean_dec(v___x_3181_);
v_a_3268_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3219_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3219_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object** _args){
lean_object* v___x_3276_ = _args[0];
lean_object* v___x_3277_ = _args[1];
lean_object* v_snd_3278_ = _args[2];
lean_object* v___x_3279_ = _args[3];
lean_object* v___x_3280_ = _args[4];
lean_object* v___x_3281_ = _args[5];
lean_object* v___x_3282_ = _args[6];
lean_object* v_a_3283_ = _args[7];
lean_object* v___x_3284_ = _args[8];
lean_object* v___x_3285_ = _args[9];
lean_object* v___x_3286_ = _args[10];
lean_object* v___x_3287_ = _args[11];
lean_object* v_params_3288_ = _args[12];
lean_object* v_args_3289_ = _args[13];
lean_object* v___x_3290_ = _args[14];
lean_object* v_a_3291_ = _args[15];
lean_object* v___x_3292_ = _args[16];
lean_object* v___f_3293_ = _args[17];
lean_object* v___x_3294_ = _args[18];
lean_object* v___x_3295_ = _args[19];
lean_object* v_numIndices_3296_ = _args[20];
lean_object* v_goalType_3297_ = _args[21];
lean_object* v___x_3298_ = _args[22];
lean_object* v___x_3299_ = _args[23];
lean_object* v_fst_3300_ = _args[24];
lean_object* v___x_3301_ = _args[25];
lean_object* v___y_3302_ = _args[26];
lean_object* v___y_3303_ = _args[27];
lean_object* v___y_3304_ = _args[28];
lean_object* v___y_3305_ = _args[29];
lean_object* v___y_3306_ = _args[30];
_start:
{
uint8_t v___x_17245__boxed_3307_; uint8_t v___x_17248__boxed_3308_; uint8_t v___x_17253__boxed_3309_; lean_object* v_res_3310_; 
v___x_17245__boxed_3307_ = lean_unbox(v___x_3277_);
v___x_17248__boxed_3308_ = lean_unbox(v___x_3280_);
v___x_17253__boxed_3309_ = lean_unbox(v___x_3285_);
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3276_, v___x_17245__boxed_3307_, v_snd_3278_, v___x_3279_, v___x_17248__boxed_3308_, v___x_3281_, v___x_3282_, v_a_3283_, v___x_3284_, v___x_17253__boxed_3309_, v___x_3286_, v___x_3287_, v_params_3288_, v_args_3289_, v___x_3290_, v_a_3291_, v___x_3292_, v___f_3293_, v___x_3294_, v___x_3295_, v_numIndices_3296_, v_goalType_3297_, v___x_3298_, v___x_3299_, v_fst_3300_, v___x_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec(v___x_3299_);
lean_dec(v___x_3298_);
return v_res_3310_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t v___x_3311_, lean_object* v_x_3312_){
_start:
{
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object* v___x_3313_, lean_object* v_x_3314_){
_start:
{
uint8_t v___x_17444__boxed_3315_; uint8_t v_res_3316_; lean_object* v_r_3317_; 
v___x_17444__boxed_3315_ = lean_unbox(v___x_3313_);
v_res_3316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_17444__boxed_3315_, v_x_3314_);
lean_dec(v_x_3314_);
v_r_3317_ = lean_box(v_res_3316_);
return v_r_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object* v___x_3321_, lean_object* v_a_3322_, lean_object* v_numIndices_3323_, lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v___x_3326_, lean_object* v___x_3327_, lean_object* v_params_3328_, lean_object* v___x_3329_, lean_object* v_a_3330_, lean_object* v___x_3331_, lean_object* v___x_3332_, lean_object* v___x_3333_, lean_object* v_args_3334_, lean_object* v_goalType_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v___x_3341_; uint8_t v___x_3342_; 
v___x_3341_ = lean_array_get_size(v_args_3334_);
v___x_3342_ = lean_nat_dec_eq(v___x_3341_, v___x_3321_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v_goalType_3335_);
lean_dec_ref(v_args_3334_);
lean_dec(v___x_3332_);
lean_dec(v___x_3331_);
lean_dec_ref(v_a_3330_);
lean_dec_ref(v___x_3329_);
lean_dec_ref(v_params_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3326_);
lean_dec(v___x_3324_);
lean_dec(v_numIndices_3323_);
lean_dec(v___x_3321_);
v___x_3343_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3344_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3343_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3344_;
}
else
{
if (lean_obj_tag(v_a_3322_) == 7)
{
lean_object* v_binderType_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v_binderType_3345_ = lean_ctor_get(v_a_3322_, 1);
lean_inc_ref(v_binderType_3345_);
v___x_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_binderType_3345_);
v___x_3347_ = 0;
v___x_3348_ = lean_box(0);
v___x_3349_ = l_Lean_Meta_mkFreshExprMVar(v___x_3346_, v___x_3347_, v___x_3348_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; lean_object* v___x_3355_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
v___x_3351_ = l_Lean_Expr_mvarId_x21(v_a_3350_);
v___x_3352_ = lean_nat_add(v_numIndices_3323_, v___x_3321_);
v___x_3353_ = lean_box(0);
v___x_3354_ = 0;
v___x_3355_ = l_Lean_Meta_introNCore(v___x_3351_, v___x_3352_, v___x_3353_, v___x_3354_, v___x_3354_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___f_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___f_3367_; lean_object* v___x_3368_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref_known(v___x_3355_, 1);
v_fst_3357_ = lean_ctor_get(v_a_3356_, 0);
lean_inc(v_fst_3357_);
v_snd_3358_ = lean_ctor_get(v_a_3356_, 1);
lean_inc_n(v_snd_3358_, 2);
lean_dec(v_a_3356_);
v___f_3359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0));
v___x_3360_ = lean_array_fget(v_args_3334_, v___x_3324_);
v___x_3361_ = lean_array_get_size(v_fst_3357_);
v___x_3362_ = lean_nat_sub(v___x_3361_, v___x_3321_);
v___x_3363_ = lean_array_get(v___x_3325_, v_fst_3357_, v___x_3362_);
v___x_3364_ = lean_box(v___x_3342_);
v___x_3365_ = lean_box(v___x_3354_);
v___x_3366_ = lean_box(v___x_3347_);
v___f_3367_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed), 31, 26);
lean_closure_set(v___f_3367_, 0, v___x_3363_);
lean_closure_set(v___f_3367_, 1, v___x_3364_);
lean_closure_set(v___f_3367_, 2, v_snd_3358_);
lean_closure_set(v___f_3367_, 3, v___x_3326_);
lean_closure_set(v___f_3367_, 4, v___x_3365_);
lean_closure_set(v___f_3367_, 5, v___x_3360_);
lean_closure_set(v___f_3367_, 6, v___x_3327_);
lean_closure_set(v___f_3367_, 7, v_a_3350_);
lean_closure_set(v___f_3367_, 8, v___x_3321_);
lean_closure_set(v___f_3367_, 9, v___x_3366_);
lean_closure_set(v___f_3367_, 10, v___x_3348_);
lean_closure_set(v___f_3367_, 11, v___x_3324_);
lean_closure_set(v___f_3367_, 12, v_params_3328_);
lean_closure_set(v___f_3367_, 13, v_args_3334_);
lean_closure_set(v___f_3367_, 14, v___x_3329_);
lean_closure_set(v___f_3367_, 15, v_a_3330_);
lean_closure_set(v___f_3367_, 16, v___x_3331_);
lean_closure_set(v___f_3367_, 17, v___f_3359_);
lean_closure_set(v___f_3367_, 18, v___x_3353_);
lean_closure_set(v___f_3367_, 19, v___x_3332_);
lean_closure_set(v___f_3367_, 20, v_numIndices_3323_);
lean_closure_set(v___f_3367_, 21, v_goalType_3335_);
lean_closure_set(v___f_3367_, 22, v___x_3362_);
lean_closure_set(v___f_3367_, 23, v___x_3361_);
lean_closure_set(v___f_3367_, 24, v_fst_3357_);
lean_closure_set(v___f_3367_, 25, v___x_3333_);
v___x_3368_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3358_, v___f_3367_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3368_;
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v_a_3350_);
lean_dec_ref(v_goalType_3335_);
lean_dec_ref(v_args_3334_);
lean_dec(v___x_3332_);
lean_dec(v___x_3331_);
lean_dec_ref(v_a_3330_);
lean_dec_ref(v___x_3329_);
lean_dec_ref(v_params_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3326_);
lean_dec(v___x_3324_);
lean_dec(v_numIndices_3323_);
lean_dec(v___x_3321_);
v_a_3369_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3355_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3355_);
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
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v_goalType_3335_);
lean_dec_ref(v_args_3334_);
lean_dec(v___x_3332_);
lean_dec(v___x_3331_);
lean_dec_ref(v_a_3330_);
lean_dec_ref(v___x_3329_);
lean_dec_ref(v_params_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3326_);
lean_dec(v___x_3324_);
lean_dec(v_numIndices_3323_);
lean_dec(v___x_3321_);
v_a_3377_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3349_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3349_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
lean_dec_ref(v_goalType_3335_);
lean_dec_ref(v_args_3334_);
lean_dec(v___x_3332_);
lean_dec(v___x_3331_);
lean_dec_ref(v_a_3330_);
lean_dec_ref(v___x_3329_);
lean_dec_ref(v_params_3328_);
lean_dec_ref(v___x_3327_);
lean_dec_ref(v___x_3326_);
lean_dec(v___x_3324_);
lean_dec(v_numIndices_3323_);
lean_dec(v___x_3321_);
v___x_3385_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3386_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3385_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
return v___x_3386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object** _args){
lean_object* v___x_3387_ = _args[0];
lean_object* v_a_3388_ = _args[1];
lean_object* v_numIndices_3389_ = _args[2];
lean_object* v___x_3390_ = _args[3];
lean_object* v___x_3391_ = _args[4];
lean_object* v___x_3392_ = _args[5];
lean_object* v___x_3393_ = _args[6];
lean_object* v_params_3394_ = _args[7];
lean_object* v___x_3395_ = _args[8];
lean_object* v_a_3396_ = _args[9];
lean_object* v___x_3397_ = _args[10];
lean_object* v___x_3398_ = _args[11];
lean_object* v___x_3399_ = _args[12];
lean_object* v_args_3400_ = _args[13];
lean_object* v_goalType_3401_ = _args[14];
lean_object* v___y_3402_ = _args[15];
lean_object* v___y_3403_ = _args[16];
lean_object* v___y_3404_ = _args[17];
lean_object* v___y_3405_ = _args[18];
lean_object* v___y_3406_ = _args[19];
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3387_, v_a_3388_, v_numIndices_3389_, v___x_3390_, v___x_3391_, v___x_3392_, v___x_3393_, v_params_3394_, v___x_3395_, v_a_3396_, v___x_3397_, v___x_3398_, v___x_3399_, v_args_3400_, v_goalType_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___x_3391_);
lean_dec_ref(v_a_3388_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; lean_object* v_env_3415_; uint8_t v___x_3416_; lean_object* v___x_3417_; 
v___x_3414_ = lean_st_ref_get(v___y_3412_);
v_env_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc_ref(v_env_3415_);
lean_dec(v___x_3414_);
v___x_3416_ = 0;
lean_inc(v_constName_3408_);
v___x_3417_ = l_Lean_Environment_findConstVal_x3f(v_env_3415_, v_constName_3408_, v___x_3416_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
return v___x_3418_;
}
else
{
lean_object* v_val_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec(v_constName_3408_);
v_val_3419_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3417_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_val_3419_);
lean_dec(v___x_3417_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set_tag(v___x_3421_, 0);
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_val_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
lean_dec(v___y_3431_);
lean_dec_ref(v___y_3430_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; 
lean_inc(v_constName_3434_);
v___x_3440_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3452_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3443_ = v___x_3440_;
v_isShared_3444_ = v_isSharedCheck_3452_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3440_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3452_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v_levelParams_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3450_; 
v_levelParams_3445_ = lean_ctor_get(v_a_3441_, 1);
lean_inc(v_levelParams_3445_);
lean_dec(v_a_3441_);
v___x_3446_ = lean_box(0);
v___x_3447_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3445_, v___x_3446_);
v___x_3448_ = l_Lean_mkConst(v_constName_3434_, v___x_3447_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3448_);
v___x_3450_ = v___x_3443_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
lean_dec(v_constName_3434_);
v_a_3453_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3440_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3440_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_){
_start:
{
lean_object* v_res_3467_; 
v_res_3467_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
return v_res_3467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v_levels_3470_, lean_object* v_params_3471_, lean_object* v___y_3472_, lean_object* v_predicates_3473_, lean_object* v_as_3474_, size_t v_sz_3475_, size_t v_i_3476_, lean_object* v_b_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
uint8_t v___x_3483_; 
v___x_3483_ = lean_usize_dec_lt(v_i_3476_, v_sz_3475_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_params_3471_);
lean_dec(v_levels_3470_);
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_b_3477_);
return v___x_3484_;
}
else
{
lean_object* v_a_3485_; lean_object* v_toConstantVal_3486_; lean_object* v_numParams_3487_; lean_object* v_numIndices_3488_; lean_object* v_name_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_a_3485_ = lean_array_uget_borrowed(v_as_3474_, v_i_3476_);
v_toConstantVal_3486_ = lean_ctor_get(v_a_3485_, 0);
v_numParams_3487_ = lean_ctor_get(v_a_3485_, 1);
v_numIndices_3488_ = lean_ctor_get(v_a_3485_, 2);
v_name_3489_ = lean_ctor_get(v_toConstantVal_3486_, 0);
lean_inc(v_name_3489_);
v___x_3490_ = l_Lean_mkCasesOnName(v_name_3489_);
lean_inc(v___x_3490_);
v___x_3491_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3490_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3493_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
lean_inc(v_a_3492_);
lean_dec_ref_known(v___x_3491_, 1);
v___x_3493_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3490_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
lean_inc_ref(v_params_3471_);
v___x_3495_ = l_Array_append___redArg(v_params_3471_, v_predicates_3473_);
v___x_3496_ = l_Lean_mkAppN(v_a_3494_, v___x_3495_);
lean_dec_ref(v___x_3495_);
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc_ref(v___x_3496_);
v___x_3497_ = lean_infer_type(v___x_3496_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
lean_inc(v___y_3481_);
lean_inc_ref(v___y_3480_);
lean_inc(v___y_3479_);
lean_inc_ref(v___y_3478_);
lean_inc_ref(v___x_3496_);
v___x_3499_ = lean_infer_type(v___x_3496_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___f_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; uint8_t v___x_3513_; lean_object* v___x_3514_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___x_3501_ = lean_unsigned_to_nat(0u);
v___x_3502_ = lean_box(0);
v___x_3503_ = lean_box(0);
lean_inc_ref(v___y_3472_);
lean_inc_ref_n(v_params_3471_, 2);
lean_inc_n(v_levels_3470_, 2);
lean_inc_n(v_name_3489_, 2);
lean_inc(v_numParams_3487_);
v___f_3504_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3504_, 0, v_numParams_3487_);
lean_closure_set(v___f_3504_, 1, v_name_3489_);
lean_closure_set(v___f_3504_, 2, v_levels_3470_);
lean_closure_set(v___f_3504_, 3, v_params_3471_);
lean_closure_set(v___f_3504_, 4, v___y_3472_);
lean_closure_set(v___f_3504_, 5, v___x_3501_);
v___x_3505_ = lean_replace_expr(v___f_3504_, v_a_3498_);
lean_dec(v_a_3498_);
lean_dec_ref(v___f_3504_);
v___x_3506_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3489_);
v___x_3507_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3506_);
v___x_3508_ = l_Lean_Name_append(v___x_3506_, v___x_3507_);
v___x_3509_ = l_Lean_mkConst(v___x_3508_, v_levels_3470_);
v___x_3510_ = lean_unsigned_to_nat(1u);
v___x_3511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3505_);
lean_inc(v_numIndices_3488_);
v___f_3512_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed), 20, 13);
lean_closure_set(v___f_3512_, 0, v___x_3510_);
lean_closure_set(v___f_3512_, 1, v_a_3500_);
lean_closure_set(v___f_3512_, 2, v_numIndices_3488_);
lean_closure_set(v___f_3512_, 3, v___x_3501_);
lean_closure_set(v___f_3512_, 4, v___x_3502_);
lean_closure_set(v___f_3512_, 5, v___x_3509_);
lean_closure_set(v___f_3512_, 6, v___x_3496_);
lean_closure_set(v___f_3512_, 7, v_params_3471_);
lean_closure_set(v___f_3512_, 8, v___x_3505_);
lean_closure_set(v___f_3512_, 9, v_a_3492_);
lean_closure_set(v___f_3512_, 10, v___x_3506_);
lean_closure_set(v___f_3512_, 11, v___x_3511_);
lean_closure_set(v___f_3512_, 12, v___x_3503_);
v___x_3513_ = 0;
v___x_3514_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_3505_, v___x_3511_, v___f_3512_, v___x_3513_, v___x_3513_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
if (lean_obj_tag(v___x_3514_) == 0)
{
size_t v___x_3515_; size_t v___x_3516_; 
lean_dec_ref_known(v___x_3514_, 1);
v___x_3515_ = ((size_t)1ULL);
v___x_3516_ = lean_usize_add(v_i_3476_, v___x_3515_);
v_i_3476_ = v___x_3516_;
v_b_3477_ = v___x_3503_;
goto _start;
}
else
{
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_params_3471_);
lean_dec(v_levels_3470_);
return v___x_3514_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3525_; 
lean_dec(v_a_3498_);
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3492_);
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_params_3471_);
lean_dec(v_levels_3470_);
v_a_3518_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3520_ = v___x_3499_;
v_isShared_3521_ = v_isSharedCheck_3525_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3499_);
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
lean_dec_ref(v___x_3496_);
lean_dec(v_a_3492_);
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_params_3471_);
lean_dec(v_levels_3470_);
v_a_3526_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3497_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3497_);
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
lean_dec(v_a_3492_);
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_params_3471_);
lean_dec(v_levels_3470_);
v_a_3534_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3493_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3493_);
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
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3549_; 
lean_dec(v___x_3490_);
lean_dec_ref(v___y_3472_);
lean_dec_ref(v_params_3471_);
lean_dec(v_levels_3470_);
v_a_3542_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3544_ = v___x_3491_;
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3491_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3549_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3547_; 
if (v_isShared_3545_ == 0)
{
v___x_3547_ = v___x_3544_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_a_3542_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v_levels_3550_, lean_object* v_params_3551_, lean_object* v___y_3552_, lean_object* v_predicates_3553_, lean_object* v_as_3554_, lean_object* v_sz_3555_, lean_object* v_i_3556_, lean_object* v_b_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
size_t v_sz_boxed_3563_; size_t v_i_boxed_3564_; lean_object* v_res_3565_; 
v_sz_boxed_3563_ = lean_unbox_usize(v_sz_3555_);
lean_dec(v_sz_3555_);
v_i_boxed_3564_ = lean_unbox_usize(v_i_3556_);
lean_dec(v_i_3556_);
v_res_3565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3550_, v_params_3551_, v___y_3552_, v_predicates_3553_, v_as_3554_, v_sz_boxed_3563_, v_i_boxed_3564_, v_b_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v_as_3554_);
lean_dec_ref(v_predicates_3553_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3566_, size_t v_sz_3567_, size_t v_i_3568_, lean_object* v_bs_3569_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_usize_dec_lt(v_i_3568_, v_sz_3567_);
if (v___x_3570_ == 0)
{
lean_dec(v_levels_3566_);
return v_bs_3569_;
}
else
{
lean_object* v_v_3571_; lean_object* v_toConstantVal_3572_; lean_object* v_name_3573_; lean_object* v___x_3574_; lean_object* v_bs_x27_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; size_t v___x_3578_; size_t v___x_3579_; lean_object* v___x_3580_; 
v_v_3571_ = lean_array_uget_borrowed(v_bs_3569_, v_i_3568_);
v_toConstantVal_3572_ = lean_ctor_get(v_v_3571_, 0);
v_name_3573_ = lean_ctor_get(v_toConstantVal_3572_, 0);
lean_inc(v_name_3573_);
v___x_3574_ = lean_unsigned_to_nat(0u);
v_bs_x27_3575_ = lean_array_uset(v_bs_3569_, v_i_3568_, v___x_3574_);
v___x_3576_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3573_);
lean_inc(v_levels_3566_);
v___x_3577_ = l_Lean_mkConst(v___x_3576_, v_levels_3566_);
v___x_3578_ = ((size_t)1ULL);
v___x_3579_ = lean_usize_add(v_i_3568_, v___x_3578_);
v___x_3580_ = lean_array_uset(v_bs_x27_3575_, v_i_3568_, v___x_3577_);
v_i_3568_ = v___x_3579_;
v_bs_3569_ = v___x_3580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3582_, lean_object* v_sz_3583_, lean_object* v_i_3584_, lean_object* v_bs_3585_){
_start:
{
size_t v_sz_boxed_3586_; size_t v_i_boxed_3587_; lean_object* v_res_3588_; 
v_sz_boxed_3586_ = lean_unbox_usize(v_sz_3583_);
lean_dec(v_sz_3583_);
v_i_boxed_3587_ = lean_unbox_usize(v_i_3584_);
lean_dec(v_i_3584_);
v_res_3588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3582_, v_sz_boxed_3586_, v_i_boxed_3587_, v_bs_3585_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3589_, lean_object* v_levels_3590_, lean_object* v___y_3591_, lean_object* v_params_3592_, lean_object* v_x_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
size_t v_sz_3599_; size_t v___x_3600_; lean_object* v_predicates_3601_; size_t v_sz_3602_; lean_object* v_predicates_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_sz_3599_ = lean_array_size(v_infos_3589_);
v___x_3600_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3589_);
lean_inc(v_levels_3590_);
v_predicates_3601_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3590_, v_sz_3599_, v___x_3600_, v_infos_3589_);
v_sz_3602_ = lean_array_size(v_predicates_3601_);
v_predicates_3603_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3592_, v_sz_3602_, v___x_3600_, v_predicates_3601_);
v___x_3604_ = lean_box(0);
v___x_3605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3590_, v_params_3592_, v___y_3591_, v_predicates_3603_, v_infos_3589_, v_sz_3599_, v___x_3600_, v___x_3604_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_);
lean_dec_ref(v_infos_3589_);
lean_dec_ref(v_predicates_3603_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v___x_3607_; uint8_t v_isShared_3608_; uint8_t v_isSharedCheck_3612_; 
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v___x_3605_, 0);
lean_dec(v_unused_3613_);
v___x_3607_ = v___x_3605_;
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
else
{
lean_dec(v___x_3605_);
v___x_3607_ = lean_box(0);
v_isShared_3608_ = v_isSharedCheck_3612_;
goto v_resetjp_3606_;
}
v_resetjp_3606_:
{
lean_object* v___x_3610_; 
if (v_isShared_3608_ == 0)
{
lean_ctor_set(v___x_3607_, 0, v___x_3604_);
v___x_3610_ = v___x_3607_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3604_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
else
{
return v___x_3605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3614_, lean_object* v_levels_3615_, lean_object* v___y_3616_, lean_object* v_params_3617_, lean_object* v_x_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3614_, v_levels_3615_, v___y_3616_, v_params_3617_, v_x_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_x_3618_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3625_, size_t v_i_3626_, size_t v_stop_3627_, lean_object* v_b_3628_){
_start:
{
uint8_t v___x_3629_; 
v___x_3629_ = lean_usize_dec_eq(v_i_3626_, v_stop_3627_);
if (v___x_3629_ == 0)
{
lean_object* v___x_3630_; lean_object* v_ctors_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; size_t v___x_3634_; size_t v___x_3635_; 
v___x_3630_ = lean_array_uget_borrowed(v_as_3625_, v_i_3626_);
v_ctors_3631_ = lean_ctor_get(v___x_3630_, 4);
lean_inc(v_ctors_3631_);
v___x_3632_ = lean_array_mk(v_ctors_3631_);
v___x_3633_ = l_Array_append___redArg(v_b_3628_, v___x_3632_);
lean_dec_ref(v___x_3632_);
v___x_3634_ = ((size_t)1ULL);
v___x_3635_ = lean_usize_add(v_i_3626_, v___x_3634_);
v_i_3626_ = v___x_3635_;
v_b_3628_ = v___x_3633_;
goto _start;
}
else
{
return v_b_3628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3637_, lean_object* v_i_3638_, lean_object* v_stop_3639_, lean_object* v_b_3640_){
_start:
{
size_t v_i_boxed_3641_; size_t v_stop_boxed_3642_; lean_object* v_res_3643_; 
v_i_boxed_3641_ = lean_unbox_usize(v_i_3638_);
lean_dec(v_i_3638_);
v_stop_boxed_3642_ = lean_unbox_usize(v_stop_3639_);
lean_dec(v_stop_3639_);
v_res_3643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3637_, v_i_boxed_3641_, v_stop_boxed_3642_, v_b_3640_);
lean_dec_ref(v_as_3637_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v_toConstantVal_3655_; lean_object* v_numParams_3656_; lean_object* v_levelParams_3657_; lean_object* v_type_3658_; lean_object* v___x_3659_; lean_object* v_levels_3660_; lean_object* v___y_3662_; lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3652_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3653_ = lean_unsigned_to_nat(0u);
v___x_3654_ = lean_array_get_borrowed(v___x_3652_, v_infos_3646_, v___x_3653_);
v_toConstantVal_3655_ = lean_ctor_get(v___x_3654_, 0);
v_numParams_3656_ = lean_ctor_get(v___x_3654_, 1);
lean_inc(v_numParams_3656_);
v_levelParams_3657_ = lean_ctor_get(v_toConstantVal_3655_, 1);
v_type_3658_ = lean_ctor_get(v_toConstantVal_3655_, 2);
lean_inc_ref(v_type_3658_);
v___x_3659_ = lean_box(0);
lean_inc(v_levelParams_3657_);
v_levels_3660_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3657_, v___x_3659_);
v___x_3669_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3670_ = lean_array_get_size(v_infos_3646_);
v___x_3671_ = lean_nat_dec_lt(v___x_3653_, v___x_3670_);
if (v___x_3671_ == 0)
{
v___y_3662_ = v___x_3669_;
goto v___jp_3661_;
}
else
{
uint8_t v___x_3672_; 
v___x_3672_ = lean_nat_dec_le(v___x_3670_, v___x_3670_);
if (v___x_3672_ == 0)
{
if (v___x_3671_ == 0)
{
v___y_3662_ = v___x_3669_;
goto v___jp_3661_;
}
else
{
size_t v___x_3673_; size_t v___x_3674_; lean_object* v___x_3675_; 
v___x_3673_ = ((size_t)0ULL);
v___x_3674_ = lean_usize_of_nat(v___x_3670_);
v___x_3675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3646_, v___x_3673_, v___x_3674_, v___x_3669_);
v___y_3662_ = v___x_3675_;
goto v___jp_3661_;
}
}
else
{
size_t v___x_3676_; size_t v___x_3677_; lean_object* v___x_3678_; 
v___x_3676_ = ((size_t)0ULL);
v___x_3677_ = lean_usize_of_nat(v___x_3670_);
v___x_3678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3646_, v___x_3676_, v___x_3677_, v___x_3669_);
v___y_3662_ = v___x_3678_;
goto v___jp_3661_;
}
}
v___jp_3661_:
{
lean_object* v___f_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; lean_object* v___x_3668_; 
lean_inc_ref(v_infos_3646_);
v___f_3663_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3663_, 0, v_infos_3646_);
lean_closure_set(v___f_3663_, 1, v_levels_3660_);
lean_closure_set(v___f_3663_, 2, v___y_3662_);
v___x_3664_ = lean_array_get_size(v_infos_3646_);
lean_dec_ref(v_infos_3646_);
v___x_3665_ = lean_nat_sub(v_numParams_3656_, v___x_3664_);
lean_dec(v_numParams_3656_);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
v___x_3667_ = 0;
v___x_3668_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_3658_, v___x_3666_, v___f_3663_, v___x_3667_, v___x_3667_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_);
return v___x_3668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
lean_object* v_res_3685_; 
v_res_3685_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3686_, lean_object* v_constName_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v___x_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3694_, lean_object* v_constName_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3694_, v_constName_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec_ref(v___y_3696_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3702_, lean_object* v_ref_3703_, lean_object* v_constName_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; 
v___x_3710_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3703_, v_constName_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3711_, lean_object* v_ref_3712_, lean_object* v_constName_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3711_, v_ref_3712_, v_constName_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v_ref_3712_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3720_, lean_object* v_ref_3721_, lean_object* v_msg_3722_, lean_object* v_declHint_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; 
v___x_3729_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3721_, v_msg_3722_, v_declHint_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3730_, lean_object* v_ref_3731_, lean_object* v_msg_3732_, lean_object* v_declHint_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3730_, v_ref_3731_, v_msg_3732_, v_declHint_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
lean_dec(v___y_3737_);
lean_dec_ref(v___y_3736_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v_ref_3731_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3740_, lean_object* v_declHint_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3740_, v_declHint_3741_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3748_, lean_object* v_declHint_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3748_, v_declHint_3749_, v___y_3750_, v___y_3751_, v___y_3752_, v___y_3753_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
lean_dec_ref(v___y_3750_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3756_, lean_object* v_ref_3757_, lean_object* v_msg_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v___x_3764_; 
v___x_3764_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3757_, v_msg_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
return v___x_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3765_, lean_object* v_ref_3766_, lean_object* v_msg_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v_res_3773_; 
v_res_3773_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3765_, v_ref_3766_, v_msg_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v_ref_3766_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3777_, lean_object* v___x_3778_, lean_object* v_params_3779_, size_t v_sz_3780_, size_t v_i_3781_, lean_object* v_bs_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_lt(v_i_3781_, v_sz_3780_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v_params_3779_);
lean_dec_ref(v___x_3778_);
lean_dec(v___x_3777_);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_bs_3782_);
return v___x_3789_;
}
else
{
lean_object* v_v_3790_; lean_object* v_toConstantVal_3791_; lean_object* v_name_3792_; lean_object* v___x_3793_; lean_object* v_bs_x27_3794_; lean_object* v___y_3796_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_v_3790_ = lean_array_uget_borrowed(v_bs_3782_, v_i_3781_);
v_toConstantVal_3791_ = lean_ctor_get(v_v_3790_, 0);
v_name_3792_ = lean_ctor_get(v_toConstantVal_3791_, 0);
lean_inc(v_name_3792_);
v___x_3793_ = lean_unsigned_to_nat(0u);
v_bs_x27_3794_ = lean_array_uset(v_bs_3782_, v_i_3781_, v___x_3793_);
v___x_3810_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3811_ = l_Lean_Name_append(v_name_3792_, v___x_3810_);
lean_inc(v___x_3777_);
v___x_3812_ = l_Lean_mkConst(v___x_3811_, v___x_3777_);
v___x_3813_ = l_Lean_Meta_unfoldDefinition(v___x_3812_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; size_t v_sz_3815_; size_t v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; uint8_t v___x_3821_; lean_object* v___x_3822_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v_sz_3815_ = lean_array_size(v___x_3778_);
v___x_3816_ = ((size_t)0ULL);
lean_inc_ref(v___x_3778_);
v___x_3817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3779_, v_sz_3815_, v___x_3816_, v___x_3778_);
lean_inc_ref(v_params_3779_);
v___x_3818_ = l_Array_append___redArg(v_params_3779_, v___x_3817_);
lean_dec_ref(v___x_3817_);
v___x_3819_ = l_Lean_mkAppN(v_a_3814_, v___x_3818_);
lean_dec_ref(v___x_3818_);
v___x_3820_ = 0;
v___x_3821_ = 1;
v___x_3822_ = l_Lean_Meta_mkLambdaFVars(v_params_3779_, v___x_3819_, v___x_3820_, v___x_3788_, v___x_3820_, v___x_3788_, v___x_3821_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
v___y_3796_ = v___x_3822_;
goto v___jp_3795_;
}
else
{
v___y_3796_ = v___x_3813_;
goto v___jp_3795_;
}
v___jp_3795_:
{
if (lean_obj_tag(v___y_3796_) == 0)
{
lean_object* v_a_3797_; size_t v___x_3798_; size_t v___x_3799_; lean_object* v___x_3800_; 
v_a_3797_ = lean_ctor_get(v___y_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___y_3796_, 1);
v___x_3798_ = ((size_t)1ULL);
v___x_3799_ = lean_usize_add(v_i_3781_, v___x_3798_);
v___x_3800_ = lean_array_uset(v_bs_x27_3794_, v_i_3781_, v_a_3797_);
v_i_3781_ = v___x_3799_;
v_bs_3782_ = v___x_3800_;
goto _start;
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v_bs_x27_3794_);
lean_dec_ref(v_params_3779_);
lean_dec_ref(v___x_3778_);
lean_dec(v___x_3777_);
v_a_3802_ = lean_ctor_get(v___y_3796_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___y_3796_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___y_3796_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___y_3796_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3823_, lean_object* v___x_3824_, lean_object* v_params_3825_, lean_object* v_sz_3826_, lean_object* v_i_3827_, lean_object* v_bs_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
size_t v_sz_boxed_3834_; size_t v_i_boxed_3835_; lean_object* v_res_3836_; 
v_sz_boxed_3834_ = lean_unbox_usize(v_sz_3826_);
lean_dec(v_sz_3826_);
v_i_boxed_3835_ = lean_unbox_usize(v_i_3827_);
lean_dec(v_i_3827_);
v_res_3836_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3823_, v___x_3824_, v_params_3825_, v_sz_boxed_3834_, v_i_boxed_3835_, v_bs_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3837_, lean_object* v___x_3838_, size_t v_sz_3839_, size_t v___x_3840_, lean_object* v_a_3841_, lean_object* v_params_3842_, lean_object* v_x_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
lean_object* v___x_3851_; 
v___x_3851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3837_, v___x_3838_, v_params_3842_, v_sz_3839_, v___x_3840_, v_a_3841_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3852_, lean_object* v___x_3853_, lean_object* v_sz_3854_, lean_object* v___x_3855_, lean_object* v_a_3856_, lean_object* v_params_3857_, lean_object* v_x_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
size_t v_sz_boxed_3866_; size_t v___x_5868__boxed_3867_; lean_object* v_res_3868_; 
v_sz_boxed_3866_ = lean_unbox_usize(v_sz_3854_);
lean_dec(v_sz_3854_);
v___x_5868__boxed_3867_ = lean_unbox_usize(v___x_3855_);
lean_dec(v___x_3855_);
v_res_3868_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3852_, v___x_3853_, v_sz_boxed_3866_, v___x_5868__boxed_3867_, v_a_3856_, v_params_3857_, v_x_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec_ref(v_x_3858_);
return v_res_3868_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(lean_object* v___x_3869_, uint8_t v___x_3870_, lean_object* v_attr_3871_){
_start:
{
lean_object* v_name_3872_; lean_object* v___x_3873_; 
v_name_3872_ = lean_ctor_get(v_attr_3871_, 0);
lean_inc(v_name_3872_);
lean_dec_ref(v_attr_3871_);
v___x_3873_ = l_Lean_getAttributeImpl(v___x_3869_, v_name_3872_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_dec_ref_known(v___x_3873_, 1);
return v___x_3870_;
}
else
{
lean_object* v_a_3874_; lean_object* v_toAttributeImplCore_3875_; uint8_t v_applicationTime_3876_; uint8_t v___x_3877_; uint8_t v___x_3878_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v_toAttributeImplCore_3875_ = lean_ctor_get(v_a_3874_, 0);
lean_inc_ref(v_toAttributeImplCore_3875_);
lean_dec(v_a_3874_);
v_applicationTime_3876_ = lean_ctor_get_uint8(v_toAttributeImplCore_3875_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_3875_);
v___x_3877_ = 1;
v___x_3878_ = l_Lean_instBEqAttributeApplicationTime_beq(v_applicationTime_3876_, v___x_3877_);
if (v___x_3878_ == 0)
{
return v___x_3870_;
}
else
{
uint8_t v___x_3879_; 
v___x_3879_ = 0;
return v___x_3879_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed(lean_object* v___x_3880_, lean_object* v___x_3881_, lean_object* v_attr_3882_){
_start:
{
uint8_t v___x_5905__boxed_3883_; uint8_t v_res_3884_; lean_object* v_r_3885_; 
v___x_5905__boxed_3883_ = lean_unbox(v___x_3881_);
v_res_3884_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(v___x_3880_, v___x_5905__boxed_3883_, v_attr_3882_);
v_r_3885_ = lean_box(v_res_3884_);
return v_r_3885_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3886_ = l_Lean_instInhabitedExpr;
v___x_3887_ = lean_box(0);
v___x_3888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
lean_ctor_set(v___x_3888_, 1, v___x_3886_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3889_, lean_object* v___x_3890_, lean_object* v_a_3891_, lean_object* v___x_3892_, size_t v_sz_3893_, size_t v_i_3894_, lean_object* v_bs_3895_){
_start:
{
uint8_t v___x_3896_; 
v___x_3896_ = lean_usize_dec_lt(v_i_3894_, v_sz_3893_);
if (v___x_3896_ == 0)
{
lean_dec(v___x_3892_);
lean_dec_ref(v___x_3890_);
return v_bs_3895_;
}
else
{
lean_object* v___x_3897_; lean_object* v_v_3898_; lean_object* v___x_3899_; lean_object* v_bs_x27_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v_modifiers_3903_; lean_object* v_ref_3904_; uint8_t v_isGreatest_3905_; lean_object* v_stx_3906_; uint8_t v_visibility_3907_; uint8_t v_isProtected_3908_; uint8_t v_computeKind_3909_; uint8_t v_recKind_3910_; uint8_t v_isUnsafe_3911_; lean_object* v_attrs_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3940_; 
v___x_3897_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v_v_3898_ = lean_array_uget(v_bs_3895_, v_i_3894_);
v___x_3899_ = lean_unsigned_to_nat(0u);
v_bs_x27_3900_ = lean_array_uset(v_bs_3895_, v_i_3894_, v___x_3899_);
v___x_3901_ = lean_usize_to_nat(v_i_3894_);
v___x_3902_ = lean_array_get_borrowed(v___x_3897_, v_coinductiveElabData_3889_, v___x_3901_);
v_modifiers_3903_ = lean_ctor_get(v___x_3902_, 3);
lean_inc_ref(v_modifiers_3903_);
v_ref_3904_ = lean_ctor_get(v___x_3902_, 2);
v_isGreatest_3905_ = lean_ctor_get_uint8(v___x_3902_, sizeof(void*)*5);
v_stx_3906_ = lean_ctor_get(v_modifiers_3903_, 0);
v_visibility_3907_ = lean_ctor_get_uint8(v_modifiers_3903_, sizeof(void*)*3);
v_isProtected_3908_ = lean_ctor_get_uint8(v_modifiers_3903_, sizeof(void*)*3 + 1);
v_computeKind_3909_ = lean_ctor_get_uint8(v_modifiers_3903_, sizeof(void*)*3 + 2);
v_recKind_3910_ = lean_ctor_get_uint8(v_modifiers_3903_, sizeof(void*)*3 + 3);
v_isUnsafe_3911_ = lean_ctor_get_uint8(v_modifiers_3903_, sizeof(void*)*3 + 4);
v_attrs_3912_ = lean_ctor_get(v_modifiers_3903_, 2);
v_isSharedCheck_3940_ = !lean_is_exclusive(v_modifiers_3903_);
if (v_isSharedCheck_3940_ == 0)
{
lean_object* v_unused_3941_; 
v_unused_3941_ = lean_ctor_get(v_modifiers_3903_, 1);
lean_dec(v_unused_3941_);
v___x_3914_ = v_modifiers_3903_;
v_isShared_3915_ = v_isSharedCheck_3940_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_attrs_3912_);
lean_inc(v_stx_3906_);
lean_dec(v_modifiers_3903_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3940_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v_fst_3918_; lean_object* v_snd_3919_; lean_object* v___x_3920_; lean_object* v___f_3921_; lean_object* v___x_3922_; lean_object* v___x_3924_; 
v___x_3916_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3917_ = lean_array_get_borrowed(v___x_3916_, v_a_3891_, v___x_3901_);
lean_dec(v___x_3901_);
v_fst_3918_ = lean_ctor_get(v___x_3917_, 0);
v_snd_3919_ = lean_ctor_get(v___x_3917_, 1);
v___x_3920_ = lean_box(v___x_3896_);
lean_inc_ref(v___x_3890_);
v___f_3921_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3921_, 0, v___x_3890_);
lean_closure_set(v___f_3921_, 1, v___x_3920_);
v___x_3922_ = lean_box(0);
if (v_isShared_3915_ == 0)
{
lean_ctor_set(v___x_3914_, 1, v___x_3922_);
v___x_3924_ = v___x_3914_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_stx_3906_);
lean_ctor_set(v_reuseFailAlloc_3939_, 1, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_3939_, 2, v_attrs_3912_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3, v_visibility_3907_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 1, v_isProtected_3908_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 2, v_computeKind_3909_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 3, v_recKind_3910_);
lean_ctor_set_uint8(v_reuseFailAlloc_3939_, sizeof(void*)*3 + 4, v_isUnsafe_3911_);
v___x_3924_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
lean_object* v___x_3925_; uint8_t v___x_3926_; uint8_t v___y_3928_; 
v___x_3925_ = l_Lean_Elab_Modifiers_filterAttrs(v___x_3924_, v___f_3921_);
v___x_3926_ = 0;
if (v_isGreatest_3905_ == 0)
{
uint8_t v___x_3937_; 
v___x_3937_ = 2;
v___y_3928_ = v___x_3937_;
goto v___jp_3927_;
}
else
{
uint8_t v___x_3938_; 
v___x_3938_ = 1;
v___y_3928_ = v___x_3938_;
goto v___jp_3927_;
}
v___jp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; size_t v___x_3933_; size_t v___x_3934_; lean_object* v___x_3935_; 
lean_inc_n(v_ref_3904_, 4);
v___x_3929_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3929_, 0, v_ref_3904_);
lean_ctor_set(v___x_3929_, 1, v___x_3922_);
lean_ctor_set_uint8(v___x_3929_, sizeof(void*)*2, v___y_3928_);
v___x_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
v___x_3931_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3931_, 0, v_ref_3904_);
lean_ctor_set(v___x_3931_, 1, v___x_3922_);
lean_ctor_set(v___x_3931_, 2, v___x_3922_);
lean_ctor_set(v___x_3931_, 3, v___x_3930_);
lean_ctor_set(v___x_3931_, 4, v___x_3922_);
lean_ctor_set(v___x_3931_, 5, v___x_3899_);
lean_inc(v_snd_3919_);
lean_inc(v_fst_3918_);
lean_inc(v___x_3892_);
v___x_3932_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3932_, 0, v_ref_3904_);
lean_ctor_set(v___x_3932_, 1, v___x_3892_);
lean_ctor_set(v___x_3932_, 2, v___x_3925_);
lean_ctor_set(v___x_3932_, 3, v_fst_3918_);
lean_ctor_set(v___x_3932_, 4, v_ref_3904_);
lean_ctor_set(v___x_3932_, 5, v___x_3899_);
lean_ctor_set(v___x_3932_, 6, v_snd_3919_);
lean_ctor_set(v___x_3932_, 7, v_v_3898_);
lean_ctor_set(v___x_3932_, 8, v___x_3931_);
lean_ctor_set_uint8(v___x_3932_, sizeof(void*)*9, v___x_3926_);
v___x_3933_ = ((size_t)1ULL);
v___x_3934_ = lean_usize_add(v_i_3894_, v___x_3933_);
v___x_3935_ = lean_array_uset(v_bs_x27_3900_, v_i_3894_, v___x_3932_);
v_i_3894_ = v___x_3934_;
v_bs_3895_ = v___x_3935_;
goto _start;
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
lean_object* v_v_4002_; lean_object* v_declName_4003_; lean_object* v___x_4004_; 
v_v_4002_ = lean_array_uget_borrowed(v_bs_3992_, v_i_3991_);
v_declName_4003_ = lean_ctor_get(v_v_4002_, 1);
lean_inc(v_declName_4003_);
v___x_4004_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_4003_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; lean_object* v___x_4006_; lean_object* v_bs_x27_4007_; size_t v___x_4008_; size_t v___x_4009_; lean_object* v___x_4010_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___x_4006_ = lean_unsigned_to_nat(0u);
v_bs_x27_4007_ = lean_array_uset(v_bs_3992_, v_i_3991_, v___x_4006_);
v___x_4008_ = ((size_t)1ULL);
v___x_4009_ = lean_usize_add(v_i_3991_, v___x_4008_);
v___x_4010_ = lean_array_uset(v_bs_x27_4007_, v_i_3991_, v_a_4005_);
v_i_3991_ = v___x_4009_;
v_bs_3992_ = v___x_4010_;
goto _start;
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
lean_dec_ref(v_bs_3992_);
v_a_4012_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4004_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4004_);
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
uint8_t v___x_6167__boxed_4101_; lean_object* v_res_4102_; 
v___x_6167__boxed_4101_ = lean_unbox(v___x_4091_);
v_res_4102_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_4088_, v___x_4089_, v___x_4090_, v___x_6167__boxed_4101_, v_args_4092_, v_body_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
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
lean_object* v_v_4116_; lean_object* v_toConstantVal_4117_; lean_object* v_name_4118_; lean_object* v_type_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___f_4122_; uint8_t v___x_4123_; lean_object* v___x_4124_; 
v_v_4116_ = lean_array_uget_borrowed(v_bs_4106_, v_i_4105_);
v_toConstantVal_4117_ = lean_ctor_get(v_v_4116_, 0);
v_name_4118_ = lean_ctor_get(v_toConstantVal_4117_, 0);
lean_inc(v_name_4118_);
v_type_4119_ = lean_ctor_get(v_toConstantVal_4117_, 2);
v___x_4120_ = lean_unsigned_to_nat(0u);
v___x_4121_ = lean_box(v___x_4114_);
lean_inc(v___x_4103_);
lean_inc(v_v_4116_);
v___f_4122_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4122_, 0, v_v_4116_);
lean_closure_set(v___f_4122_, 1, v___x_4120_);
lean_closure_set(v___f_4122_, 2, v___x_4103_);
lean_closure_set(v___f_4122_, 3, v___x_4121_);
v___x_4123_ = 0;
lean_inc_ref(v_type_4119_);
v___x_4124_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4119_, v___f_4122_, v___x_4123_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v_bs_x27_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; size_t v___x_4129_; size_t v___x_4130_; lean_object* v___x_4131_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v_bs_x27_4126_ = lean_array_uset(v_bs_4106_, v_i_4105_, v___x_4120_);
v___x_4127_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4118_);
v___x_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
lean_ctor_set(v___x_4128_, 1, v_a_4125_);
v___x_4129_ = ((size_t)1ULL);
v___x_4130_ = lean_usize_add(v_i_4105_, v___x_4129_);
v___x_4131_ = lean_array_uset(v_bs_x27_4126_, v_i_4105_, v___x_4128_);
v_i_4105_ = v___x_4130_;
v_bs_4106_ = v___x_4131_;
goto _start;
}
else
{
lean_object* v_a_4133_; lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
lean_dec(v_name_4118_);
lean_dec_ref(v_bs_4106_);
lean_dec(v___x_4103_);
v_a_4133_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4140_ == 0)
{
v___x_4135_ = v___x_4124_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_inc(v_a_4133_);
lean_dec(v___x_4124_);
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
lean_object* v_options_4187_; lean_object* v_inheritedTraceOptions_4188_; uint8_t v_hasTrace_4189_; lean_object* v___x_4190_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; 
v_options_4187_ = lean_ctor_get(v_a_4184_, 2);
v_inheritedTraceOptions_4188_ = lean_ctor_get(v_a_4184_, 13);
v_hasTrace_4189_ = lean_ctor_get_uint8(v_options_4187_, sizeof(void*)*1);
v___x_4190_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4189_ == 0)
{
v___y_4192_ = v_a_4180_;
v___y_4193_ = v_a_4181_;
v___y_4194_ = v_a_4182_;
v___y_4195_ = v_a_4183_;
v___y_4196_ = v_a_4184_;
v___y_4197_ = v_a_4185_;
goto v___jp_4191_;
}
else
{
lean_object* v_cls_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v_cls_4259_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4260_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4261_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4188_, v_options_4187_, v___x_4260_);
if (v___x_4261_ == 0)
{
v___y_4192_ = v_a_4180_;
v___y_4193_ = v_a_4181_;
v___y_4194_ = v_a_4182_;
v___y_4195_ = v_a_4183_;
v___y_4196_ = v_a_4184_;
v___y_4197_ = v_a_4185_;
goto v___jp_4191_;
}
else
{
lean_object* v___x_4262_; size_t v_sz_4263_; size_t v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4262_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4263_ = lean_array_size(v_coinductiveElabData_4179_);
v___x_4264_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4179_);
v___x_4265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4263_, v___x_4264_, v_coinductiveElabData_4179_);
v___x_4266_ = lean_array_to_list(v___x_4265_);
v___x_4267_ = lean_box(0);
v___x_4268_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4266_, v___x_4267_);
v___x_4269_ = l_Lean_MessageData_ofList(v___x_4268_);
v___x_4270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4262_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4259_, v___x_4270_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
if (lean_obj_tag(v___x_4271_) == 0)
{
lean_dec_ref_known(v___x_4271_, 1);
v___y_4192_ = v_a_4180_;
v___y_4193_ = v_a_4181_;
v___y_4194_ = v_a_4182_;
v___y_4195_ = v_a_4183_;
v___y_4196_ = v_a_4184_;
v___y_4197_ = v_a_4185_;
goto v___jp_4191_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4179_);
return v___x_4271_;
}
}
}
v___jp_4191_:
{
size_t v_sz_4198_; size_t v___x_4199_; lean_object* v___x_4200_; 
v_sz_4198_ = lean_array_size(v_coinductiveElabData_4179_);
v___x_4199_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4179_);
v___x_4200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4198_, v___x_4199_, v_coinductiveElabData_4179_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v_toConstantVal_4204_; lean_object* v_numParams_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; size_t v_sz_4208_; lean_object* v___x_4209_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc_n(v_a_4201_, 2);
lean_dec_ref_known(v___x_4200_, 1);
v___x_4202_ = lean_unsigned_to_nat(0u);
v___x_4203_ = lean_array_get_borrowed(v___x_4190_, v_a_4201_, v___x_4202_);
v_toConstantVal_4204_ = lean_ctor_get(v___x_4203_, 0);
v_numParams_4205_ = lean_ctor_get(v___x_4203_, 1);
v___x_4206_ = lean_array_get_size(v_a_4201_);
v___x_4207_ = lean_nat_sub(v_numParams_4205_, v___x_4206_);
v_sz_4208_ = lean_array_size(v_a_4201_);
lean_inc(v___x_4207_);
v___x_4209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4207_, v_sz_4208_, v___x_4199_, v_a_4201_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v_levelParams_4211_; lean_object* v_type_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; size_t v_sz_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___f_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; lean_object* v___x_4222_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc_n(v_a_4210_, 2);
lean_dec_ref_known(v___x_4209_, 1);
v_levelParams_4211_ = lean_ctor_get(v_toConstantVal_4204_, 1);
v_type_4212_ = lean_ctor_get(v_toConstantVal_4204_, 2);
v___x_4213_ = lean_box(0);
lean_inc(v_levelParams_4211_);
v___x_4214_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4211_, v___x_4213_);
v_sz_4215_ = lean_array_size(v_a_4210_);
lean_inc(v___x_4214_);
v___x_4216_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4214_, v_sz_4215_, v___x_4199_, v_a_4210_);
v___x_4217_ = lean_box_usize(v_sz_4208_);
v___x_4218_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4201_);
v___f_4219_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4219_, 0, v___x_4214_);
lean_closure_set(v___f_4219_, 1, v___x_4216_);
lean_closure_set(v___f_4219_, 2, v___x_4217_);
lean_closure_set(v___f_4219_, 3, v___x_4218_);
lean_closure_set(v___f_4219_, 4, v_a_4201_);
lean_inc(v___x_4207_);
v___x_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4207_);
v___x_4221_ = 0;
lean_inc_ref(v_type_4212_);
v___x_4222_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4212_, v___x_4220_, v___f_4219_, v___x_4221_, v___x_4221_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4224_; lean_object* v_env_4225_; size_t v_sz_4226_; lean_object* v_lctx_4227_; lean_object* v_localInstances_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4222_, 1);
v___x_4224_ = lean_st_ref_get(v___y_4197_);
v_env_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc_ref(v_env_4225_);
lean_dec(v___x_4224_);
v_sz_4226_ = lean_array_size(v_a_4223_);
v_lctx_4227_ = lean_ctor_get(v___y_4194_, 2);
v_localInstances_4228_ = lean_ctor_get(v___y_4194_, 3);
lean_inc(v_levelParams_4211_);
v___x_4229_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4179_, v_env_4225_, v_a_4210_, v_levelParams_4211_, v_sz_4226_, v___x_4199_, v_a_4223_);
lean_dec(v_a_4210_);
lean_inc_ref(v_localInstances_4228_);
lean_inc_ref(v_lctx_4227_);
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v_lctx_4227_);
lean_ctor_set(v___x_4230_, 1, v_localInstances_4228_);
v___x_4231_ = l_Lean_Elab_partialFixpoint(v___x_4230_, v___x_4229_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4232_; 
lean_dec_ref_known(v___x_4231_, 1);
lean_inc(v_a_4201_);
v___x_4232_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4201_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v___x_4233_; 
lean_dec_ref_known(v___x_4232_, 1);
lean_inc(v_a_4201_);
v___x_4233_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4207_, v_a_4201_, v_coinductiveElabData_4179_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4234_; 
lean_dec_ref_known(v___x_4233_, 1);
v___x_4234_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4201_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
return v___x_4234_;
}
else
{
lean_dec(v_a_4201_);
return v___x_4233_;
}
}
else
{
lean_dec(v___x_4207_);
lean_dec(v_a_4201_);
lean_dec_ref(v_coinductiveElabData_4179_);
return v___x_4232_;
}
}
else
{
lean_dec(v___x_4207_);
lean_dec(v_a_4201_);
lean_dec_ref(v_coinductiveElabData_4179_);
return v___x_4231_;
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_a_4210_);
lean_dec(v___x_4207_);
lean_dec(v_a_4201_);
lean_dec_ref(v_coinductiveElabData_4179_);
v_a_4235_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4222_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4222_);
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
lean_dec(v___x_4207_);
lean_dec(v_a_4201_);
lean_dec_ref(v_coinductiveElabData_4179_);
v_a_4243_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4209_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4209_);
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
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec_ref(v_coinductiveElabData_4179_);
v_a_4251_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4200_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4200_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4281_, lean_object* v___x_4282_, lean_object* v_params_4283_, size_t v_sz_4284_, size_t v_i_4285_, lean_object* v_bs_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4281_, v___x_4282_, v_params_4283_, v_sz_4284_, v_i_4285_, v_bs_4286_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4295_, lean_object* v___x_4296_, lean_object* v_params_4297_, lean_object* v_sz_4298_, lean_object* v_i_4299_, lean_object* v_bs_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
size_t v_sz_boxed_4308_; size_t v_i_boxed_4309_; lean_object* v_res_4310_; 
v_sz_boxed_4308_ = lean_unbox_usize(v_sz_4298_);
lean_dec(v_sz_4298_);
v_i_boxed_4309_ = lean_unbox_usize(v_i_4299_);
lean_dec(v_i_4299_);
v_res_4310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4295_, v___x_4296_, v_params_4297_, v_sz_boxed_4308_, v_i_boxed_4309_, v_bs_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4311_, lean_object* v___x_4312_, lean_object* v_a_4313_, lean_object* v___x_4314_, lean_object* v_as_4315_, size_t v_sz_4316_, size_t v_i_4317_, lean_object* v_bs_4318_){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4311_, v___x_4312_, v_a_4313_, v___x_4314_, v_sz_4316_, v_i_4317_, v_bs_4318_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4320_, lean_object* v___x_4321_, lean_object* v_a_4322_, lean_object* v___x_4323_, lean_object* v_as_4324_, lean_object* v_sz_4325_, lean_object* v_i_4326_, lean_object* v_bs_4327_){
_start:
{
size_t v_sz_boxed_4328_; size_t v_i_boxed_4329_; lean_object* v_res_4330_; 
v_sz_boxed_4328_ = lean_unbox_usize(v_sz_4325_);
lean_dec(v_sz_4325_);
v_i_boxed_4329_ = lean_unbox_usize(v_i_4326_);
lean_dec(v_i_4326_);
v_res_4330_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4320_, v___x_4321_, v_a_4322_, v___x_4323_, v_as_4324_, v_sz_boxed_4328_, v_i_boxed_4329_, v_bs_4327_);
lean_dec_ref(v_as_4324_);
lean_dec_ref(v_a_4322_);
lean_dec_ref(v_coinductiveElabData_4320_);
return v_res_4330_;
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
