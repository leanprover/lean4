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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_getAttributeImpl(lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t, uint8_t);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = l_Lean_Expr_hasMVar(v_e_171_);
v___x_175_ = lean_bool_not(v___x_174_);
if (v___x_175_ == 0)
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
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v_e_171_);
return v___x_196_;
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
v___x_397_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_449_; lean_object* v_vs_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_470_; 
v_ks_449_ = lean_ctor_get(v_x_398_, 0);
v_vs_450_ = lean_ctor_get(v_x_398_, 1);
v_isSharedCheck_470_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_470_ == 0)
{
v___x_452_ = v_x_398_;
v_isShared_453_ = v_isSharedCheck_470_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_vs_450_);
lean_inc(v_ks_449_);
lean_dec(v_x_398_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_470_;
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
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_ks_449_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_vs_450_);
v___x_455_ = v_reuseFailAlloc_469_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v_newNode_456_; uint8_t v___y_458_; size_t v___x_464_; uint8_t v___x_465_; 
v_newNode_456_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__12___redArg(v___x_455_, v_x_401_, v_x_402_);
v___x_464_ = ((size_t)7ULL);
v___x_465_ = lean_usize_dec_le(v___x_464_, v_x_400_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_466_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_456_);
v___x_467_ = lean_unsigned_to_nat(4u);
v___x_468_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
lean_dec(v___x_466_);
v___y_458_ = v___x_468_;
goto v___jp_457_;
}
else
{
v___y_458_ = v___x_465_;
goto v___jp_457_;
}
v___jp_457_:
{
if (v___y_458_ == 0)
{
lean_object* v_ks_459_; lean_object* v_vs_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_ks_459_ = lean_ctor_get(v_newNode_456_, 0);
lean_inc_ref(v_ks_459_);
v_vs_460_ = lean_ctor_get(v_newNode_456_, 1);
lean_inc_ref(v_vs_460_);
lean_dec_ref(v_newNode_456_);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___closed__0);
v___x_463_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_x_400_, v_ks_459_, v_vs_460_, v___x_461_, v___x_462_);
lean_dec_ref(v_vs_460_);
lean_dec_ref(v_ks_459_);
return v___x_463_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(size_t v_depth_471_, lean_object* v_keys_472_, lean_object* v_vals_473_, lean_object* v_i_474_, lean_object* v_entries_475_){
_start:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_array_get_size(v_keys_472_);
v___x_477_ = lean_nat_dec_lt(v_i_474_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec(v_i_474_);
return v_entries_475_;
}
else
{
lean_object* v_k_478_; lean_object* v_v_479_; uint64_t v___x_480_; size_t v_h_481_; size_t v___x_482_; lean_object* v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; size_t v_h_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_k_478_ = lean_array_fget_borrowed(v_keys_472_, v_i_474_);
v_v_479_ = lean_array_fget_borrowed(v_vals_473_, v_i_474_);
v___x_480_ = l_Lean_instHashableMVarId_hash(v_k_478_);
v_h_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = ((size_t)5ULL);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_sub(v_depth_471_, v___x_484_);
v___x_486_ = lean_usize_mul(v___x_482_, v___x_485_);
v_h_487_ = lean_usize_shift_right(v_h_481_, v___x_486_);
v___x_488_ = lean_nat_add(v_i_474_, v___x_483_);
lean_dec(v_i_474_);
lean_inc(v_v_479_);
lean_inc(v_k_478_);
v___x_489_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_entries_475_, v_h_487_, v_depth_471_, v_k_478_, v_v_479_);
v_i_474_ = v___x_488_;
v_entries_475_ = v___x_489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg___boxed(lean_object* v_depth_491_, lean_object* v_keys_492_, lean_object* v_vals_493_, lean_object* v_i_494_, lean_object* v_entries_495_){
_start:
{
size_t v_depth_boxed_496_; lean_object* v_res_497_; 
v_depth_boxed_496_ = lean_unbox_usize(v_depth_491_);
lean_dec(v_depth_491_);
v_res_497_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9_spec__13___redArg(v_depth_boxed_496_, v_keys_492_, v_vals_493_, v_i_494_, v_entries_495_);
lean_dec_ref(v_vals_493_);
lean_dec_ref(v_keys_492_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg___boxed(lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
size_t v_x_8771__boxed_503_; size_t v_x_8772__boxed_504_; lean_object* v_res_505_; 
v_x_8771__boxed_503_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_x_8772__boxed_504_ = lean_unbox_usize(v_x_500_);
lean_dec(v_x_500_);
v_res_505_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_498_, v_x_8771__boxed_503_, v_x_8772__boxed_504_, v_x_501_, v_x_502_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(lean_object* v_x_506_, lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
uint64_t v___x_509_; size_t v___x_510_; size_t v___x_511_; lean_object* v___x_512_; 
v___x_509_ = l_Lean_instHashableMVarId_hash(v_x_507_);
v___x_510_ = lean_uint64_to_usize(v___x_509_);
v___x_511_ = ((size_t)1ULL);
v___x_512_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5_spec__9___redArg(v_x_506_, v___x_510_, v___x_511_, v_x_507_, v_x_508_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(lean_object* v_mvarId_513_, lean_object* v_val_514_, lean_object* v___y_515_){
_start:
{
lean_object* v___x_517_; lean_object* v_mctx_518_; lean_object* v_cache_519_; lean_object* v_zetaDeltaFVarIds_520_; lean_object* v_postponed_521_; lean_object* v_diag_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_550_; 
v___x_517_ = lean_st_ref_take(v___y_515_);
v_mctx_518_ = lean_ctor_get(v___x_517_, 0);
v_cache_519_ = lean_ctor_get(v___x_517_, 1);
v_zetaDeltaFVarIds_520_ = lean_ctor_get(v___x_517_, 2);
v_postponed_521_ = lean_ctor_get(v___x_517_, 3);
v_diag_522_ = lean_ctor_get(v___x_517_, 4);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_550_ == 0)
{
v___x_524_ = v___x_517_;
v_isShared_525_ = v_isSharedCheck_550_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_diag_522_);
lean_inc(v_postponed_521_);
lean_inc(v_zetaDeltaFVarIds_520_);
lean_inc(v_cache_519_);
lean_inc(v_mctx_518_);
lean_dec(v___x_517_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_550_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v_depth_526_; lean_object* v_levelAssignDepth_527_; lean_object* v_lmvarCounter_528_; lean_object* v_mvarCounter_529_; lean_object* v_lDecls_530_; lean_object* v_decls_531_; lean_object* v_userNames_532_; lean_object* v_lAssignment_533_; lean_object* v_eAssignment_534_; lean_object* v_dAssignment_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_549_; 
v_depth_526_ = lean_ctor_get(v_mctx_518_, 0);
v_levelAssignDepth_527_ = lean_ctor_get(v_mctx_518_, 1);
v_lmvarCounter_528_ = lean_ctor_get(v_mctx_518_, 2);
v_mvarCounter_529_ = lean_ctor_get(v_mctx_518_, 3);
v_lDecls_530_ = lean_ctor_get(v_mctx_518_, 4);
v_decls_531_ = lean_ctor_get(v_mctx_518_, 5);
v_userNames_532_ = lean_ctor_get(v_mctx_518_, 6);
v_lAssignment_533_ = lean_ctor_get(v_mctx_518_, 7);
v_eAssignment_534_ = lean_ctor_get(v_mctx_518_, 8);
v_dAssignment_535_ = lean_ctor_get(v_mctx_518_, 9);
v_isSharedCheck_549_ = !lean_is_exclusive(v_mctx_518_);
if (v_isSharedCheck_549_ == 0)
{
v___x_537_ = v_mctx_518_;
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_dAssignment_535_);
lean_inc(v_eAssignment_534_);
lean_inc(v_lAssignment_533_);
lean_inc(v_userNames_532_);
lean_inc(v_decls_531_);
lean_inc(v_lDecls_530_);
lean_inc(v_mvarCounter_529_);
lean_inc(v_lmvarCounter_528_);
lean_inc(v_levelAssignDepth_527_);
lean_inc(v_depth_526_);
lean_dec(v_mctx_518_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_539_; lean_object* v___x_541_; 
v___x_539_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_534_, v_mvarId_513_, v_val_514_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 8, v___x_539_);
v___x_541_ = v___x_537_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_depth_526_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_levelAssignDepth_527_);
lean_ctor_set(v_reuseFailAlloc_548_, 2, v_lmvarCounter_528_);
lean_ctor_set(v_reuseFailAlloc_548_, 3, v_mvarCounter_529_);
lean_ctor_set(v_reuseFailAlloc_548_, 4, v_lDecls_530_);
lean_ctor_set(v_reuseFailAlloc_548_, 5, v_decls_531_);
lean_ctor_set(v_reuseFailAlloc_548_, 6, v_userNames_532_);
lean_ctor_set(v_reuseFailAlloc_548_, 7, v_lAssignment_533_);
lean_ctor_set(v_reuseFailAlloc_548_, 8, v___x_539_);
lean_ctor_set(v_reuseFailAlloc_548_, 9, v_dAssignment_535_);
v___x_541_ = v_reuseFailAlloc_548_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_543_; 
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_541_);
v___x_543_ = v___x_524_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_cache_519_);
lean_ctor_set(v_reuseFailAlloc_547_, 2, v_zetaDeltaFVarIds_520_);
lean_ctor_set(v_reuseFailAlloc_547_, 3, v_postponed_521_);
lean_ctor_set(v_reuseFailAlloc_547_, 4, v_diag_522_);
v___x_543_ = v_reuseFailAlloc_547_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_st_ref_set(v___y_515_, v___x_543_);
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
v___x_827_ = lean_st_ref_set(v___y_788_, v___x_826_);
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
uint8_t v___x_1086_; uint8_t v___x_1087_; 
v___x_1086_ = l_Lean_Expr_hasMVar(v_e_1083_);
v___x_1087_ = lean_bool_not(v___x_1086_);
if (v___x_1087_ == 0)
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
v___x_1103_ = lean_st_ref_set(v___y_1084_, v___x_1102_);
v___x_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_fst_1091_);
return v___x_1104_;
}
}
}
else
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_e_1083_);
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg___boxed(lean_object* v_e_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1109_, v___y_1110_);
lean_dec(v___y_1110_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(lean_object* v_e_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___redArg(v_e_1113_, v___y_1117_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4___boxed(lean_object* v_e_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__4(v_e_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
lean_dec(v___y_1126_);
lean_dec_ref(v___y_1125_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(lean_object* v_k_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v_b_1134_, lean_object* v_c_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
lean_object* v___x_1141_; 
lean_inc(v___y_1139_);
lean_inc_ref(v___y_1138_);
lean_inc(v___y_1137_);
lean_inc_ref(v___y_1136_);
lean_inc(v___y_1133_);
lean_inc_ref(v___y_1132_);
v___x_1141_ = lean_apply_9(v_k_1131_, v_b_1134_, v_c_1135_, v___y_1132_, v___y_1133_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, lean_box(0));
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed(lean_object* v_k_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v_b_1145_, lean_object* v_c_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v_res_1152_; 
v_res_1152_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0(v_k_1142_, v___y_1143_, v___y_1144_, v_b_1145_, v_c_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(lean_object* v_type_1153_, lean_object* v_k_1154_, uint8_t v_cleanupAnnotations_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___f_1163_; uint8_t v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
v___f_1163_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1163_, 0, v_k_1154_);
lean_closure_set(v___f_1163_, 1, v___y_1156_);
lean_closure_set(v___f_1163_, 2, v___y_1157_);
v___x_1164_ = 0;
v___x_1165_ = lean_box(0);
v___x_1166_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1164_, v___x_1165_, v_type_1153_, v___f_1163_, v_cleanupAnnotations_1155_, v___x_1164_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
if (lean_obj_tag(v___x_1166_) == 0)
{
return v___x_1166_;
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1166_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1166_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___boxed(lean_object* v_type_1175_, lean_object* v_k_1176_, lean_object* v_cleanupAnnotations_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1185_; lean_object* v_res_1186_; 
v_cleanupAnnotations_boxed_1185_ = lean_unbox(v_cleanupAnnotations_1177_);
v_res_1186_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1175_, v_k_1176_, v_cleanupAnnotations_boxed_1185_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(lean_object* v_00_u03b1_1187_, lean_object* v_type_1188_, lean_object* v_k_1189_, uint8_t v_cleanupAnnotations_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_1188_, v_k_1189_, v_cleanupAnnotations_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_type_1200_, lean_object* v_k_1201_, lean_object* v_cleanupAnnotations_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1210_; lean_object* v_res_1211_; 
v_cleanupAnnotations_boxed_1210_ = lean_unbox(v_cleanupAnnotations_1202_);
v_res_1211_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6(v_00_u03b1_1199_, v_type_1200_, v_k_1201_, v_cleanupAnnotations_boxed_1210_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(lean_object* v_name_1212_, lean_object* v_levelParams_1213_, lean_object* v_type_1214_, lean_object* v_value_1215_, lean_object* v_hints_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; uint8_t v___y_1221_; uint8_t v___y_1228_; lean_object* v_env_1231_; uint8_t v___x_1232_; 
v___x_1219_ = lean_st_ref_get(v___y_1217_);
v_env_1231_ = lean_ctor_get(v___x_1219_, 0);
lean_inc_ref_n(v_env_1231_, 2);
lean_dec(v___x_1219_);
v___x_1232_ = l_Lean_Environment_hasUnsafe(v_env_1231_, v_type_1214_);
if (v___x_1232_ == 0)
{
uint8_t v___x_1233_; 
v___x_1233_ = l_Lean_Environment_hasUnsafe(v_env_1231_, v_value_1215_);
v___y_1228_ = v___x_1233_;
goto v___jp_1227_;
}
else
{
lean_dec_ref(v_env_1231_);
v___y_1228_ = v___x_1232_;
goto v___jp_1227_;
}
v___jp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_inc(v_name_1212_);
v___x_1222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1222_, 0, v_name_1212_);
lean_ctor_set(v___x_1222_, 1, v_levelParams_1213_);
lean_ctor_set(v___x_1222_, 2, v_type_1214_);
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_name_1212_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1225_, 0, v___x_1222_);
lean_ctor_set(v___x_1225_, 1, v_value_1215_);
lean_ctor_set(v___x_1225_, 2, v_hints_1216_);
lean_ctor_set(v___x_1225_, 3, v___x_1224_);
lean_ctor_set_uint8(v___x_1225_, sizeof(void*)*4, v___y_1221_);
v___x_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
return v___x_1226_;
}
v___jp_1227_:
{
if (v___y_1228_ == 0)
{
uint8_t v___x_1229_; 
v___x_1229_ = 1;
v___y_1221_ = v___x_1229_;
goto v___jp_1220_;
}
else
{
uint8_t v___x_1230_; 
v___x_1230_ = 0;
v___y_1221_ = v___x_1230_;
goto v___jp_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg___boxed(lean_object* v_name_1234_, lean_object* v_levelParams_1235_, lean_object* v_type_1236_, lean_object* v_value_1237_, lean_object* v_hints_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1234_, v_levelParams_1235_, v_type_1236_, v_value_1237_, v_hints_1238_, v___y_1239_);
lean_dec(v___y_1239_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(lean_object* v_name_1242_, lean_object* v_levelParams_1243_, lean_object* v_type_1244_, lean_object* v_value_1245_, lean_object* v_hints_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___redArg(v_name_1242_, v_levelParams_1243_, v_type_1244_, v_value_1245_, v_hints_1246_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7___boxed(lean_object* v_name_1255_, lean_object* v_levelParams_1256_, lean_object* v_type_1257_, lean_object* v_value_1258_, lean_object* v_hints_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__7(v_name_1255_, v_levelParams_1256_, v_type_1257_, v_value_1258_, v_hints_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(lean_object* v_type_1268_, lean_object* v_maxFVars_x3f_1269_, lean_object* v_k_1270_, uint8_t v_cleanupAnnotations_1271_, uint8_t v_whnfType_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___f_1280_; lean_object* v___x_1281_; 
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
v___f_1280_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1280_, 0, v_k_1270_);
lean_closure_set(v___f_1280_, 1, v___y_1273_);
lean_closure_set(v___f_1280_, 2, v___y_1274_);
v___x_1281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_1268_, v_maxFVars_x3f_1269_, v___f_1280_, v_cleanupAnnotations_1271_, v_whnfType_1272_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1281_) == 0)
{
return v___x_1281_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1281_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1281_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1281_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg___boxed(lean_object* v_type_1290_, lean_object* v_maxFVars_x3f_1291_, lean_object* v_k_1292_, lean_object* v_cleanupAnnotations_1293_, lean_object* v_whnfType_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1302_; uint8_t v_whnfType_boxed_1303_; lean_object* v_res_1304_; 
v_cleanupAnnotations_boxed_1302_ = lean_unbox(v_cleanupAnnotations_1293_);
v_whnfType_boxed_1303_ = lean_unbox(v_whnfType_1294_);
v_res_1304_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1290_, v_maxFVars_x3f_1291_, v_k_1292_, v_cleanupAnnotations_boxed_1302_, v_whnfType_boxed_1303_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(lean_object* v_00_u03b1_1305_, lean_object* v_type_1306_, lean_object* v_maxFVars_x3f_1307_, lean_object* v_k_1308_, uint8_t v_cleanupAnnotations_1309_, uint8_t v_whnfType_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_1306_, v_maxFVars_x3f_1307_, v_k_1308_, v_cleanupAnnotations_1309_, v_whnfType_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___boxed(lean_object* v_00_u03b1_1319_, lean_object* v_type_1320_, lean_object* v_maxFVars_x3f_1321_, lean_object* v_k_1322_, lean_object* v_cleanupAnnotations_1323_, lean_object* v_whnfType_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1332_; uint8_t v_whnfType_boxed_1333_; lean_object* v_res_1334_; 
v_cleanupAnnotations_boxed_1332_ = lean_unbox(v_cleanupAnnotations_1323_);
v_whnfType_boxed_1333_ = lean_unbox(v_whnfType_1324_);
v_res_1334_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8(v_00_u03b1_1319_, v_type_1320_, v_maxFVars_x3f_1321_, v_k_1322_, v_cleanupAnnotations_boxed_1332_, v_whnfType_boxed_1333_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(lean_object* v_cls_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_options_1343_; uint8_t v_hasTrace_1344_; 
v_options_1343_ = lean_ctor_get(v___y_1340_, 2);
v_hasTrace_1344_ = lean_ctor_get_uint8(v_options_1343_, sizeof(void*)*1);
if (v_hasTrace_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
lean_dec(v_cls_1335_);
v___x_1345_ = lean_box(v_hasTrace_1344_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
return v___x_1346_;
}
else
{
lean_object* v_inheritedTraceOptions_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_inheritedTraceOptions_1347_ = lean_ctor_get(v___y_1340_, 13);
v___x_1348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__3));
v___x_1349_ = l_Lean_Name_append(v___x_1348_, v_cls_1335_);
v___x_1350_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1347_, v_options_1343_, v___x_1349_);
lean_dec(v___x_1349_);
v___x_1351_ = lean_box(v___x_1350_);
v___x_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0___boxed(lean_object* v_cls_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__0(v_cls_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__3___redArg(lean_object* v_mvarId_1362_, lean_object* v_val_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; lean_object* v_mctx_1367_; lean_object* v_cache_1368_; lean_object* v_zetaDeltaFVarIds_1369_; lean_object* v_postponed_1370_; lean_object* v_diag_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1399_; 
v___x_1366_ = lean_st_ref_take(v___y_1364_);
v_mctx_1367_ = lean_ctor_get(v___x_1366_, 0);
v_cache_1368_ = lean_ctor_get(v___x_1366_, 1);
v_zetaDeltaFVarIds_1369_ = lean_ctor_get(v___x_1366_, 2);
v_postponed_1370_ = lean_ctor_get(v___x_1366_, 3);
v_diag_1371_ = lean_ctor_get(v___x_1366_, 4);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1373_ = v___x_1366_;
v_isShared_1374_ = v_isSharedCheck_1399_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_diag_1371_);
lean_inc(v_postponed_1370_);
lean_inc(v_zetaDeltaFVarIds_1369_);
lean_inc(v_cache_1368_);
lean_inc(v_mctx_1367_);
lean_dec(v___x_1366_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1399_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v_depth_1375_; lean_object* v_levelAssignDepth_1376_; lean_object* v_lmvarCounter_1377_; lean_object* v_mvarCounter_1378_; lean_object* v_lDecls_1379_; lean_object* v_decls_1380_; lean_object* v_userNames_1381_; lean_object* v_lAssignment_1382_; lean_object* v_eAssignment_1383_; lean_object* v_dAssignment_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1398_; 
v_depth_1375_ = lean_ctor_get(v_mctx_1367_, 0);
v_levelAssignDepth_1376_ = lean_ctor_get(v_mctx_1367_, 1);
v_lmvarCounter_1377_ = lean_ctor_get(v_mctx_1367_, 2);
v_mvarCounter_1378_ = lean_ctor_get(v_mctx_1367_, 3);
v_lDecls_1379_ = lean_ctor_get(v_mctx_1367_, 4);
v_decls_1380_ = lean_ctor_get(v_mctx_1367_, 5);
v_userNames_1381_ = lean_ctor_get(v_mctx_1367_, 6);
v_lAssignment_1382_ = lean_ctor_get(v_mctx_1367_, 7);
v_eAssignment_1383_ = lean_ctor_get(v_mctx_1367_, 8);
v_dAssignment_1384_ = lean_ctor_get(v_mctx_1367_, 9);
v_isSharedCheck_1398_ = !lean_is_exclusive(v_mctx_1367_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1386_ = v_mctx_1367_;
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_dAssignment_1384_);
lean_inc(v_eAssignment_1383_);
lean_inc(v_lAssignment_1382_);
lean_inc(v_userNames_1381_);
lean_inc(v_decls_1380_);
lean_inc(v_lDecls_1379_);
lean_inc(v_mvarCounter_1378_);
lean_inc(v_lmvarCounter_1377_);
lean_inc(v_levelAssignDepth_1376_);
lean_inc(v_depth_1375_);
lean_dec(v_mctx_1367_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1398_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
v___x_1388_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4_spec__5___redArg(v_eAssignment_1383_, v_mvarId_1362_, v_val_1363_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 8, v___x_1388_);
v___x_1390_ = v___x_1386_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v_depth_1375_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_levelAssignDepth_1376_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_lmvarCounter_1377_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_mvarCounter_1378_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_lDecls_1379_);
lean_ctor_set(v_reuseFailAlloc_1397_, 5, v_decls_1380_);
lean_ctor_set(v_reuseFailAlloc_1397_, 6, v_userNames_1381_);
lean_ctor_set(v_reuseFailAlloc_1397_, 7, v_lAssignment_1382_);
lean_ctor_set(v_reuseFailAlloc_1397_, 8, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1397_, 9, v_dAssignment_1384_);
v___x_1390_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 0, v___x_1390_);
v___x_1392_ = v___x_1373_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_cache_1368_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_zetaDeltaFVarIds_1369_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_postponed_1370_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_diag_1371_);
v___x_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = lean_st_ref_set(v___y_1364_, v___x_1392_);
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
v___x_1449_ = lean_st_ref_set(v___y_1410_, v___x_1448_);
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
lean_object* v_options_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; uint8_t v___x_2073_; 
v_options_2070_ = lean_ctor_get(v___y_2068_, 2);
v___x_2071_ = l_Lean_Elab_pp_macroStack;
v___x_2072_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1_spec__5(v_options_2070_, v___x_2071_);
v___x_2073_ = lean_bool_not(v___x_2072_);
if (v___x_2073_ == 0)
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
else
{
lean_object* v___x_2093_; 
lean_dec(v_macroStack_2067_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_msgData_2066_);
return v___x_2093_;
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
lean_object* v_ref_2107_; lean_object* v___x_2108_; lean_object* v_a_2109_; lean_object* v_macroStack_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2121_; 
v_ref_2107_ = lean_ctor_get(v___y_2104_, 5);
v___x_2108_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1_spec__1(v_msg_2099_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref(v___x_2108_);
v_macroStack_2110_ = lean_ctor_get(v___y_2100_, 1);
v___x_2111_ = l_Lean_Elab_getBetterRef(v_ref_2107_, v_macroStack_2110_);
lean_inc(v_macroStack_2110_);
v___x_2112_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0_spec__0_spec__1___redArg(v_a_2109_, v_macroStack_2110_, v___y_2104_);
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
lean_ctor_set(v___x_2117_, 0, v___x_2111_);
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
lean_object* v___x_2228_; 
lean_inc(v_head_2218_);
v___x_2228_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0(v_head_2218_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_toConstantVal_2229_; lean_object* v_a_2230_; lean_object* v_name_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v_toConstantVal_2229_ = lean_ctor_get(v_a_2205_, 0);
v_a_2230_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2230_);
lean_dec_ref_known(v___x_2228_, 1);
v_name_2231_ = lean_ctor_get(v_toConstantVal_2229_, 0);
v___x_2232_ = lean_array_fget_borrowed(v_array_2220_, v_start_2221_);
lean_inc(v_name_2231_);
lean_inc(v_numParams_2207_);
lean_inc(v___x_2232_);
lean_inc_ref(v_infos_2206_);
v___x_2233_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor(v_infos_2206_, v___x_2232_, v_numParams_2207_, v_name_2231_, v_a_2230_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
lean_dec_ref_known(v___x_2233_, 1);
v___x_2234_ = lean_unsigned_to_nat(1u);
v___x_2235_ = lean_nat_add(v_start_2221_, v___x_2234_);
lean_dec(v_start_2221_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2235_);
v___x_2237_ = v___x_2226_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_array_2220_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_stop_2222_);
v___x_2237_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
v_as_x27_2208_ = v_tail_2219_;
v_b_2209_ = v___x_2237_;
goto _start;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_del_object(v___x_2226_);
lean_dec(v_stop_2222_);
lean_dec(v_start_2221_);
lean_dec_ref(v_array_2220_);
lean_dec(v_numParams_2207_);
lean_dec_ref(v_infos_2206_);
lean_dec_ref(v_a_2205_);
v_a_2240_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2233_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2233_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_del_object(v___x_2226_);
lean_dec(v_stop_2222_);
lean_dec(v_start_2221_);
lean_dec_ref(v_array_2220_);
lean_dec(v_numParams_2207_);
lean_dec_ref(v_infos_2206_);
lean_dec_ref(v_a_2205_);
v_a_2248_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2228_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2228_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
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
lean_object* v___x_2296_; lean_object* v_ctorSyntax_2297_; lean_object* v_a_2298_; lean_object* v_ctors_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2296_ = lean_array_fget_borrowed(v_array_2288_, v_start_2289_);
v_ctorSyntax_2297_ = lean_ctor_get(v___x_2296_, 4);
v_a_2298_ = lean_array_uget_borrowed(v_as_2275_, v_i_2277_);
v_ctors_2299_ = lean_ctor_get(v_a_2298_, 4);
v___x_2300_ = lean_array_get_size(v_ctorSyntax_2297_);
v___x_2301_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_ctorSyntax_2297_);
v___x_2302_ = l_Array_toSubarray___redArg(v_ctorSyntax_2297_, v___x_2301_, v___x_2300_);
lean_inc(v_numParams_2274_);
lean_inc_ref(v_infos_2273_);
lean_inc(v_a_2298_);
v___x_2303_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__1___redArg(v_a_2298_, v_infos_2273_, v_numParams_2274_, v_ctors_2299_, v___x_2302_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2303_, 1);
v___x_2304_ = lean_unsigned_to_nat(1u);
v___x_2305_ = lean_nat_add(v_start_2289_, v___x_2304_);
lean_dec(v_start_2289_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2305_);
v___x_2307_ = v___x_2294_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_array_2288_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v___x_2305_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v_stop_2290_);
v___x_2307_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
size_t v___x_2308_; size_t v___x_2309_; 
v___x_2308_ = ((size_t)1ULL);
v___x_2309_ = lean_usize_add(v_i_2277_, v___x_2308_);
v_i_2277_ = v___x_2309_;
v_b_2278_ = v___x_2307_;
goto _start;
}
}
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_del_object(v___x_2294_);
lean_dec(v_stop_2290_);
lean_dec(v_start_2289_);
lean_dec_ref(v_array_2288_);
lean_dec(v_numParams_2274_);
lean_dec_ref(v_infos_2273_);
v_a_2312_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2303_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2303_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
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
lean_object* v_fileName_2578_; lean_object* v_fileMap_2579_; lean_object* v_options_2580_; lean_object* v_currRecDepth_2581_; lean_object* v_maxRecDepth_2582_; lean_object* v_ref_2583_; lean_object* v_currNamespace_2584_; lean_object* v_openDecls_2585_; lean_object* v_initHeartbeats_2586_; lean_object* v_maxHeartbeats_2587_; lean_object* v_quotContext_2588_; lean_object* v_currMacroScope_2589_; uint8_t v_diag_2590_; lean_object* v_cancelTk_x3f_2591_; uint8_t v_suppressElabErrors_2592_; lean_object* v_inheritedTraceOptions_2593_; lean_object* v_ref_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v_fileName_2578_ = lean_ctor_get(v___y_2575_, 0);
v_fileMap_2579_ = lean_ctor_get(v___y_2575_, 1);
v_options_2580_ = lean_ctor_get(v___y_2575_, 2);
v_currRecDepth_2581_ = lean_ctor_get(v___y_2575_, 3);
v_maxRecDepth_2582_ = lean_ctor_get(v___y_2575_, 4);
v_ref_2583_ = lean_ctor_get(v___y_2575_, 5);
v_currNamespace_2584_ = lean_ctor_get(v___y_2575_, 6);
v_openDecls_2585_ = lean_ctor_get(v___y_2575_, 7);
v_initHeartbeats_2586_ = lean_ctor_get(v___y_2575_, 8);
v_maxHeartbeats_2587_ = lean_ctor_get(v___y_2575_, 9);
v_quotContext_2588_ = lean_ctor_get(v___y_2575_, 10);
v_currMacroScope_2589_ = lean_ctor_get(v___y_2575_, 11);
v_diag_2590_ = lean_ctor_get_uint8(v___y_2575_, sizeof(void*)*14);
v_cancelTk_x3f_2591_ = lean_ctor_get(v___y_2575_, 12);
v_suppressElabErrors_2592_ = lean_ctor_get_uint8(v___y_2575_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2593_ = lean_ctor_get(v___y_2575_, 13);
v_ref_2594_ = l_Lean_replaceRef(v_ref_2571_, v_ref_2583_);
lean_inc_ref(v_inheritedTraceOptions_2593_);
lean_inc(v_cancelTk_x3f_2591_);
lean_inc(v_currMacroScope_2589_);
lean_inc(v_quotContext_2588_);
lean_inc(v_maxHeartbeats_2587_);
lean_inc(v_initHeartbeats_2586_);
lean_inc(v_openDecls_2585_);
lean_inc(v_currNamespace_2584_);
lean_inc(v_maxRecDepth_2582_);
lean_inc(v_currRecDepth_2581_);
lean_inc_ref(v_options_2580_);
lean_inc_ref(v_fileMap_2579_);
lean_inc_ref(v_fileName_2578_);
v___x_2595_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2595_, 0, v_fileName_2578_);
lean_ctor_set(v___x_2595_, 1, v_fileMap_2579_);
lean_ctor_set(v___x_2595_, 2, v_options_2580_);
lean_ctor_set(v___x_2595_, 3, v_currRecDepth_2581_);
lean_ctor_set(v___x_2595_, 4, v_maxRecDepth_2582_);
lean_ctor_set(v___x_2595_, 5, v_ref_2594_);
lean_ctor_set(v___x_2595_, 6, v_currNamespace_2584_);
lean_ctor_set(v___x_2595_, 7, v_openDecls_2585_);
lean_ctor_set(v___x_2595_, 8, v_initHeartbeats_2586_);
lean_ctor_set(v___x_2595_, 9, v_maxHeartbeats_2587_);
lean_ctor_set(v___x_2595_, 10, v_quotContext_2588_);
lean_ctor_set(v___x_2595_, 11, v_currMacroScope_2589_);
lean_ctor_set(v___x_2595_, 12, v_cancelTk_x3f_2591_);
lean_ctor_set(v___x_2595_, 13, v_inheritedTraceOptions_2593_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*14, v_diag_2590_);
lean_ctor_set_uint8(v___x_2595_, sizeof(void*)*14 + 1, v_suppressElabErrors_2592_);
v___x_2596_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v_msg_2572_, v___y_2573_, v___y_2574_, v___x_2595_, v___y_2576_);
lean_dec_ref_known(v___x_2595_, 14);
return v___x_2596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_ref_2597_, lean_object* v_msg_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2597_, v_msg_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v_ref_2597_);
return v_res_2604_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2605_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__0);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2609_ = lean_unsigned_to_nat(0u);
v___x_2610_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_ctor_set(v___x_2610_, 2, v___x_2609_);
lean_ctor_set(v___x_2610_, 3, v___x_2609_);
lean_ctor_set(v___x_2610_, 4, v___x_2608_);
lean_ctor_set(v___x_2610_, 5, v___x_2608_);
lean_ctor_set(v___x_2610_, 6, v___x_2608_);
lean_ctor_set(v___x_2610_, 7, v___x_2608_);
lean_ctor_set(v___x_2610_, 8, v___x_2608_);
lean_ctor_set(v___x_2610_, 9, v___x_2608_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_unsigned_to_nat(32u);
v___x_2612_ = lean_mk_empty_array_with_capacity(v___x_2611_);
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4(void){
_start:
{
size_t v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2614_ = ((size_t)5ULL);
v___x_2615_ = lean_unsigned_to_nat(0u);
v___x_2616_ = lean_unsigned_to_nat(32u);
v___x_2617_ = lean_mk_empty_array_with_capacity(v___x_2616_);
v___x_2618_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__3);
v___x_2619_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
lean_ctor_set(v___x_2619_, 1, v___x_2617_);
lean_ctor_set(v___x_2619_, 2, v___x_2615_);
lean_ctor_set(v___x_2619_, 3, v___x_2615_);
lean_ctor_set_usize(v___x_2619_, 4, v___x_2614_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2620_ = lean_box(1);
v___x_2621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__4);
v___x_2622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__1);
v___x_2623_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___x_2621_);
lean_ctor_set(v___x_2623_, 2, v___x_2620_);
return v___x_2623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__6));
v___x_2626_ = l_Lean_stringToMessageData(v___x_2625_);
return v___x_2626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__8));
v___x_2629_ = l_Lean_stringToMessageData(v___x_2628_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__10));
v___x_2632_ = l_Lean_stringToMessageData(v___x_2631_);
return v___x_2632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__12));
v___x_2635_ = l_Lean_stringToMessageData(v___x_2634_);
return v___x_2635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__15(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__14));
v___x_2638_ = l_Lean_stringToMessageData(v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__17(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__16));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__19(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___closed__18));
v___x_2644_ = l_Lean_stringToMessageData(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(lean_object* v_msg_2645_, lean_object* v_declHint_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; lean_object* v_env_2650_; uint8_t v___y_2652_; uint8_t v___x_2708_; uint8_t v___x_2709_; 
v___x_2649_ = lean_st_ref_get(v___y_2647_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2650_);
lean_dec(v___x_2649_);
v___x_2708_ = l_Lean_Name_isAnonymous(v_declHint_2646_);
v___x_2709_ = lean_bool_not(v___x_2708_);
if (v___x_2709_ == 0)
{
v___y_2652_ = v___x_2709_;
goto v___jp_2651_;
}
else
{
uint8_t v_isExporting_2710_; 
v_isExporting_2710_ = lean_ctor_get_uint8(v_env_2650_, sizeof(void*)*8);
v___y_2652_ = v_isExporting_2710_;
goto v___jp_2651_;
}
v___jp_2651_:
{
if (v___y_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref(v_env_2650_);
lean_dec(v_declHint_2646_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_msg_2645_);
return v___x_2653_;
}
else
{
uint8_t v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v___x_2654_ = 0;
lean_inc_ref(v_env_2650_);
v___x_2655_ = l_Lean_Environment_setExporting(v_env_2650_, v___x_2654_);
lean_inc(v_declHint_2646_);
lean_inc_ref(v___x_2655_);
v___x_2656_ = l_Lean_Environment_contains(v___x_2655_, v_declHint_2646_, v___y_2652_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
lean_dec_ref(v___x_2655_);
lean_dec_ref(v_env_2650_);
lean_dec(v_declHint_2646_);
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_msg_2645_);
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
lean_inc(v_declHint_2646_);
v___x_2662_ = l_Lean_MessageData_ofConstName(v_declHint_2646_, v___x_2654_);
v_c_2663_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2663_, 0, v___x_2661_);
lean_ctor_set(v_c_2663_, 1, v___x_2662_);
v___x_2664_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2650_, v_declHint_2646_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v_env_2650_);
lean_dec(v_declHint_2646_);
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
lean_ctor_set(v___x_2670_, 0, v_msg_2645_);
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
v___x_2677_ = l_Lean_Environment_header(v_env_2650_);
lean_dec_ref(v_env_2650_);
v___x_2678_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2677_);
v_mod_2679_ = lean_array_get(v___x_2676_, v___x_2678_, v_val_2672_);
lean_dec(v_val_2672_);
lean_dec_ref(v___x_2678_);
v___x_2680_ = l_Lean_isPrivateName(v_declHint_2646_);
lean_dec(v_declHint_2646_);
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
lean_ctor_set(v___x_2690_, 0, v_msg_2645_);
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
lean_ctor_set(v___x_2703_, 0, v_msg_2645_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg___boxed(lean_object* v_msg_2711_, lean_object* v_declHint_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2711_, v_declHint_2712_, v___y_2713_);
lean_dec(v___y_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(lean_object* v_msg_2716_, lean_object* v_declHint_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2733_; 
v___x_2723_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_2716_, v_declHint_2717_, v___y_2721_);
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2733_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2733_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2728_ = l_Lean_unknownIdentifierMessageTag;
v___x_2729_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v_a_2724_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2729_);
v___x_2731_ = v___x_2726_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11___boxed(lean_object* v_msg_2734_, lean_object* v_declHint_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2734_, v_declHint_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(lean_object* v_ref_2742_, lean_object* v_msg_2743_, lean_object* v_declHint_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; lean_object* v_a_2751_; lean_object* v___x_2752_; 
v___x_2750_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11(v_msg_2743_, v_declHint_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_2742_, v_a_2751_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_ref_2753_, lean_object* v_msg_2754_, lean_object* v_declHint_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2753_, v_msg_2754_, v_declHint_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
lean_dec(v___y_2759_);
lean_dec_ref(v___y_2758_);
lean_dec(v___y_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v_ref_2753_);
return v_res_2761_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__0));
v___x_2764_ = l_Lean_stringToMessageData(v___x_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(lean_object* v_ref_2765_, lean_object* v_constName_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; uint8_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2772_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___closed__1);
v___x_2773_ = 0;
lean_inc(v_constName_2766_);
v___x_2774_ = l_Lean_MessageData_ofConstName(v_constName_2766_, v___x_2773_);
v___x_2775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2775_, 0, v___x_2772_);
lean_ctor_set(v___x_2775_, 1, v___x_2774_);
v___x_2776_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors_spec__0___closed__1);
v___x_2777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2775_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_2765_, v___x_2777_, v_constName_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg___boxed(lean_object* v_ref_2779_, lean_object* v_constName_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2779_, v_constName_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v_ref_2779_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(lean_object* v_constName_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v_ref_2793_; lean_object* v___x_2794_; 
v_ref_2793_ = lean_ctor_get(v___y_2790_, 5);
v___x_2794_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_2793_, v_constName_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg___boxed(lean_object* v_constName_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec(v___y_2799_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(lean_object* v_constName_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; lean_object* v_env_2809_; uint8_t v___x_2810_; lean_object* v___x_2811_; 
v___x_2808_ = lean_st_ref_get(v___y_2806_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v___x_2810_ = 0;
lean_inc(v_constName_2802_);
v___x_2811_ = l_Lean_Environment_find_x3f(v_env_2809_, v_constName_2802_, v___x_2810_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v___x_2812_; 
v___x_2812_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
return v___x_2812_;
}
else
{
lean_object* v_val_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v_constName_2802_);
v_val_2813_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2811_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_val_2813_);
lean_dec(v___x_2811_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
lean_ctor_set_tag(v___x_2815_, 0);
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_val_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2___boxed(lean_object* v_constName_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v_constName_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
return v_res_2827_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(lean_object* v_e_2828_, lean_object* v_as_2829_, size_t v_i_2830_, size_t v_stop_2831_){
_start:
{
uint8_t v___x_2832_; 
v___x_2832_ = lean_usize_dec_eq(v_i_2830_, v_stop_2831_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2833_ = lean_array_uget_borrowed(v_as_2829_, v_i_2830_);
v___x_2834_ = l_Lean_Expr_isAppOf(v_e_2828_, v___x_2833_);
if (v___x_2834_ == 0)
{
size_t v___x_2835_; size_t v___x_2836_; 
v___x_2835_ = ((size_t)1ULL);
v___x_2836_ = lean_usize_add(v_i_2830_, v___x_2835_);
v_i_2830_ = v___x_2836_;
goto _start;
}
else
{
return v___x_2834_;
}
}
else
{
uint8_t v___x_2838_; 
v___x_2838_ = 0;
return v___x_2838_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1___boxed(lean_object* v_e_2839_, lean_object* v_as_2840_, lean_object* v_i_2841_, lean_object* v_stop_2842_){
_start:
{
size_t v_i_boxed_2843_; size_t v_stop_boxed_2844_; uint8_t v_res_2845_; lean_object* v_r_2846_; 
v_i_boxed_2843_ = lean_unbox_usize(v_i_2841_);
lean_dec(v_i_2841_);
v_stop_boxed_2844_ = lean_unbox_usize(v_stop_2842_);
lean_dec(v_stop_2842_);
v_res_2845_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2839_, v_as_2840_, v_i_boxed_2843_, v_stop_boxed_2844_);
lean_dec_ref(v_as_2840_);
lean_dec_ref(v_e_2839_);
v_r_2846_ = lean_box(v_res_2845_);
return v_r_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(lean_object* v_numParams_2847_, lean_object* v_name_2848_, lean_object* v_levels_2849_, lean_object* v_params_2850_, lean_object* v___y_2851_, lean_object* v___x_2852_, lean_object* v_e_2853_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = l_Lean_Expr_isApp(v_e_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec_ref(v_e_2853_);
lean_dec_ref(v_params_2850_);
lean_dec(v_levels_2849_);
lean_dec(v_name_2848_);
lean_dec(v_numParams_2847_);
v___x_2855_ = lean_box(0);
return v___x_2855_;
}
else
{
lean_object* v_dummy_2856_; lean_object* v_nargs_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___y_2865_; uint8_t v___x_2875_; 
v_dummy_2856_ = lean_obj_once(&l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0, &l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0_once, _init_l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___lam__1___closed__0);
v_nargs_2857_ = l_Lean_Expr_getAppNumArgs(v_e_2853_);
lean_inc(v_nargs_2857_);
v___x_2858_ = lean_mk_array(v_nargs_2857_, v_dummy_2856_);
v___x_2859_ = lean_unsigned_to_nat(1u);
v___x_2860_ = lean_nat_sub(v_nargs_2857_, v___x_2859_);
lean_dec(v_nargs_2857_);
lean_inc_ref(v_e_2853_);
v___x_2861_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2853_, v___x_2858_, v___x_2860_);
v___x_2862_ = lean_array_get_size(v___x_2861_);
v___x_2863_ = l_Array_toSubarray___redArg(v___x_2861_, v_numParams_2847_, v___x_2862_);
v___x_2875_ = l_Lean_Expr_isAppOf(v_e_2853_, v_name_2848_);
if (v___x_2875_ == 0)
{
lean_object* v___x_2876_; uint8_t v___x_2877_; 
lean_dec(v_name_2848_);
v___x_2876_ = lean_array_get_size(v___y_2851_);
v___x_2877_ = lean_nat_dec_lt(v___x_2852_, v___x_2876_);
if (v___x_2877_ == 0)
{
v___y_2865_ = v___x_2875_;
goto v___jp_2864_;
}
else
{
if (v___x_2877_ == 0)
{
v___y_2865_ = v___x_2875_;
goto v___jp_2864_;
}
else
{
size_t v___x_2878_; size_t v___x_2879_; uint8_t v___x_2880_; 
v___x_2878_ = ((size_t)0ULL);
v___x_2879_ = lean_usize_of_nat(v___x_2876_);
v___x_2880_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__1(v_e_2853_, v___y_2851_, v___x_2878_, v___x_2879_);
v___y_2865_ = v___x_2880_;
goto v___jp_2864_;
}
}
}
else
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_dec_ref(v_e_2853_);
v___x_2881_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_2848_);
v___x_2882_ = l_Lean_mkConst(v___x_2881_, v_levels_2849_);
v___x_2883_ = l_Subarray_copy___redArg(v___x_2863_);
v___x_2884_ = l_Array_append___redArg(v_params_2850_, v___x_2883_);
lean_dec_ref(v___x_2883_);
v___x_2885_ = l_Lean_mkAppN(v___x_2882_, v___x_2884_);
lean_dec_ref(v___x_2884_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
v___jp_2864_:
{
if (v___y_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec_ref(v___x_2863_);
lean_dec_ref(v_e_2853_);
lean_dec_ref(v_params_2850_);
lean_dec(v_levels_2849_);
v___x_2866_ = lean_box(0);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2867_ = l_Lean_Expr_getAppFn(v_e_2853_);
lean_dec_ref(v_e_2853_);
v___x_2868_ = l_Lean_Expr_constName(v___x_2867_);
lean_dec_ref(v___x_2867_);
v___x_2869_ = l_Lean_Elab_Command_removeFunctorPostfixInCtor(v___x_2868_);
v___x_2870_ = l_Lean_mkConst(v___x_2869_, v_levels_2849_);
v___x_2871_ = l_Subarray_copy___redArg(v___x_2863_);
v___x_2872_ = l_Array_append___redArg(v_params_2850_, v___x_2871_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed(lean_object* v_numParams_2887_, lean_object* v_name_2888_, lean_object* v_levels_2889_, lean_object* v_params_2890_, lean_object* v___y_2891_, lean_object* v___x_2892_, lean_object* v_e_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0(v_numParams_2887_, v_name_2888_, v_levels_2889_, v_params_2890_, v___y_2891_, v___x_2892_, v_e_2893_);
lean_dec(v___x_2892_);
lean_dec_ref(v___y_2891_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(lean_object* v_eqProof_2895_, lean_object* v___x_2896_, lean_object* v_eNew_2897_, lean_object* v_snd_2898_, lean_object* v___x_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Meta_mkEqMP(v_eqProof_2895_, v___x_2896_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_a_2906_);
lean_dec_ref_known(v___x_2905_, 1);
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_eNew_2897_);
v___x_2908_ = lean_box(0);
v___x_2909_ = l_Lean_MVarId_replace(v_snd_2898_, v___x_2899_, v_a_2906_, v___x_2907_, v___x_2908_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
return v___x_2909_;
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_dec(v___x_2899_);
lean_dec(v_snd_2898_);
lean_dec_ref(v_eNew_2897_);
v_a_2910_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2905_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2905_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed(lean_object* v_eqProof_2918_, lean_object* v___x_2919_, lean_object* v_eNew_2920_, lean_object* v_snd_2921_, lean_object* v___x_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2(v_eqProof_2918_, v___x_2919_, v_eNew_2920_, v_snd_2921_, v___x_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec(v___y_2924_);
lean_dec_ref(v___y_2923_);
return v_res_2928_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__0));
v___x_2931_ = l_Lean_stringToMessageData(v___x_2930_);
return v___x_2931_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__9));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(lean_object* v___x_2955_, lean_object* v___x_2956_, uint8_t v___x_2957_, lean_object* v___x_2958_, lean_object* v___x_2959_, uint8_t v___x_2960_, lean_object* v___x_2961_, lean_object* v_params_2962_, lean_object* v_args_2963_, lean_object* v_indices_2964_, uint8_t v___x_2965_, lean_object* v___x_2966_, lean_object* v_a_2967_, lean_object* v___x_2968_, lean_object* v___f_2969_, lean_object* v___x_2970_, lean_object* v_targetArgs_2971_, lean_object* v_x_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_){
_start:
{
lean_object* v___x_2978_; uint8_t v___x_2979_; 
v___x_2978_ = lean_array_get_size(v_targetArgs_2971_);
v___x_2979_ = lean_nat_dec_eq(v___x_2978_, v___x_2955_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v___x_2956_);
v___x_2980_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_2981_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_2980_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
return v___x_2981_;
}
else
{
lean_object* v___x_2982_; 
lean_inc(v___y_2976_);
lean_inc_ref(v___y_2975_);
lean_inc(v___y_2974_);
lean_inc_ref(v___y_2973_);
lean_inc_ref(v___x_2956_);
v___x_2982_ = lean_infer_type(v___x_2956_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
if (lean_obj_tag(v_a_2983_) == 7)
{
lean_object* v_binderType_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_binderType_2984_ = lean_ctor_get(v_a_2983_, 1);
lean_inc_ref(v_binderType_2984_);
lean_dec_ref_known(v_a_2983_, 3);
v___x_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2985_, 0, v_binderType_2984_);
v___x_2986_ = l_Lean_Meta_mkFreshExprMVar(v___x_2985_, v___x_2957_, v___x_2958_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = l_Lean_Expr_mvarId_x21(v_a_2987_);
v___x_2989_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_rewriteGoalUsingEq(v___x_2988_, v___x_2959_, v___x_2960_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = lean_array_fget_borrowed(v_targetArgs_2971_, v___x_2961_);
lean_inc(v___x_2991_);
v___x_2992_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_a_2990_, v___x_2991_, v___y_2974_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3074_; 
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___x_2992_, 0);
lean_dec(v_unused_3075_);
v___x_2994_ = v___x_2992_;
v_isShared_2995_ = v_isSharedCheck_3074_;
goto v_resetjp_2993_;
}
else
{
lean_dec(v___x_2992_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3074_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; 
v___x_2996_ = l_Lean_Expr_app___override(v___x_2956_, v_a_2987_);
lean_inc_ref(v_params_2962_);
v___x_2997_ = l_Array_append___redArg(v_params_2962_, v_args_2963_);
v___x_2998_ = l_Array_append___redArg(v___x_2997_, v_indices_2964_);
v___x_2999_ = l_Array_append___redArg(v___x_2998_, v_targetArgs_2971_);
v___x_3000_ = 1;
v___x_3001_ = l_Lean_Meta_mkLambdaFVars(v___x_2999_, v___x_2996_, v___x_2965_, v___x_2960_, v___x_2965_, v___x_2960_, v___x_3000_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec_ref(v___x_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__5___redArg(v_a_3002_, v___y_2974_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = l_Lean_Meta_mkForallFVars(v_params_2962_, v___x_2966_, v___x_2965_, v___x_2960_, v___x_2960_, v___x_3000_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec_ref(v_params_2962_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref_known(v___x_3005_, 1);
v___x_3007_ = l_Lean_ConstantInfo_levelParams(v_a_2967_);
v___x_3008_ = l_Lean_mkCasesOnName(v___x_2968_);
v___x_3009_ = lean_box(0);
lean_inc(v___x_3008_);
v___x_3010_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__7___redArg(v___x_3008_, v___x_3007_, v_a_3006_, v_a_3004_, v___x_3009_, v___y_2976_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3013_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
if (v_isShared_2995_ == 0)
{
lean_ctor_set_tag(v___x_2994_, 1);
lean_ctor_set(v___x_2994_, 0, v_a_3011_);
v___x_3013_ = v___x_2994_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3011_);
v___x_3013_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_Lean_addDecl(v___x_3013_, v___x_2965_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3014_, 1);
v___x_3015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__8));
v___x_3016_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_applyAttributes___boxed), 9, 2);
lean_closure_set(v___x_3016_, 0, v___x_3008_);
lean_closure_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = lean_box(0);
v___x_3018_ = lean_box(0);
v___x_3019_ = lean_box(1);
v___x_3020_ = lean_mk_empty_array_with_capacity(v___x_2961_);
v___x_3021_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_3021_, 0, v___x_3017_);
lean_ctor_set(v___x_3021_, 1, v___x_3018_);
lean_ctor_set(v___x_3021_, 2, v___x_3017_);
lean_ctor_set(v___x_3021_, 3, v___f_2969_);
lean_ctor_set(v___x_3021_, 4, v___x_3019_);
lean_ctor_set(v___x_3021_, 5, v___x_3019_);
lean_ctor_set(v___x_3021_, 6, v___x_3017_);
lean_ctor_set(v___x_3021_, 7, v___x_3020_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8, v___x_2960_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 1, v___x_2960_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 2, v___x_2960_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 3, v___x_2960_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 4, v___x_2965_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 5, v___x_2965_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 6, v___x_2965_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 7, v___x_2965_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 8, v___x_2960_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 9, v___x_2965_);
lean_ctor_set_uint8(v___x_3021_, sizeof(void*)*8 + 10, v___x_2960_);
v___x_3022_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3022_, 0, v___x_2970_);
lean_ctor_set(v___x_3022_, 1, v___x_3019_);
lean_ctor_set(v___x_3022_, 2, v___x_3018_);
lean_ctor_set(v___x_3022_, 3, v___x_3018_);
lean_ctor_set(v___x_3022_, 4, v___x_3018_);
lean_ctor_set(v___x_3022_, 5, v___x_3019_);
lean_ctor_set(v___x_3022_, 6, v___x_3018_);
v___x_3023_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_3016_, v___x_3021_, v___x_3022_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3032_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3032_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3032_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_fst_3028_; lean_object* v___x_3030_; 
v_fst_3028_ = lean_ctor_get(v_a_3024_, 0);
lean_inc(v_fst_3028_);
lean_dec(v_a_3024_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_fst_3028_);
v___x_3030_ = v___x_3026_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_fst_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
v_a_3033_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3023_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3023_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
else
{
lean_dec(v___x_3008_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
return v___x_3014_;
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec(v___x_3008_);
lean_del_object(v___x_2994_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
v_a_3042_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3010_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3010_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec(v_a_3004_);
lean_del_object(v___x_2994_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
v_a_3050_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3005_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3005_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
if (v_isShared_3053_ == 0)
{
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v_a_3050_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_del_object(v___x_2994_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
v_a_3058_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3003_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3003_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_del_object(v___x_2994_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
v_a_3066_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3001_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3001_);
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
else
{
lean_dec(v_a_2987_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
lean_dec_ref(v___x_2956_);
return v___x_2992_;
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_2987_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
lean_dec_ref(v___x_2956_);
v_a_3076_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_2989_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_2989_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
lean_dec_ref(v___x_2959_);
lean_dec_ref(v___x_2956_);
v_a_3084_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_2986_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_2986_);
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
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec(v_a_2983_);
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v___x_2956_);
v___x_3092_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3093_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3092_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
return v___x_3093_;
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v___x_2970_);
lean_dec_ref(v___f_2969_);
lean_dec(v___x_2968_);
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_params_2962_);
lean_dec_ref(v___x_2959_);
lean_dec(v___x_2958_);
lean_dec_ref(v___x_2956_);
v_a_3094_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_2982_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_2982_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed(lean_object** _args){
lean_object* v___x_3102_ = _args[0];
lean_object* v___x_3103_ = _args[1];
lean_object* v___x_3104_ = _args[2];
lean_object* v___x_3105_ = _args[3];
lean_object* v___x_3106_ = _args[4];
lean_object* v___x_3107_ = _args[5];
lean_object* v___x_3108_ = _args[6];
lean_object* v_params_3109_ = _args[7];
lean_object* v_args_3110_ = _args[8];
lean_object* v_indices_3111_ = _args[9];
lean_object* v___x_3112_ = _args[10];
lean_object* v___x_3113_ = _args[11];
lean_object* v_a_3114_ = _args[12];
lean_object* v___x_3115_ = _args[13];
lean_object* v___f_3116_ = _args[14];
lean_object* v___x_3117_ = _args[15];
lean_object* v_targetArgs_3118_ = _args[16];
lean_object* v_x_3119_ = _args[17];
lean_object* v___y_3120_ = _args[18];
lean_object* v___y_3121_ = _args[19];
lean_object* v___y_3122_ = _args[20];
lean_object* v___y_3123_ = _args[21];
lean_object* v___y_3124_ = _args[22];
_start:
{
uint8_t v___x_16846__boxed_3125_; uint8_t v___x_16849__boxed_3126_; uint8_t v___x_16851__boxed_3127_; lean_object* v_res_3128_; 
v___x_16846__boxed_3125_ = lean_unbox(v___x_3104_);
v___x_16849__boxed_3126_ = lean_unbox(v___x_3107_);
v___x_16851__boxed_3127_ = lean_unbox(v___x_3112_);
v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3(v___x_3102_, v___x_3103_, v___x_16846__boxed_3125_, v___x_3105_, v___x_3106_, v___x_16849__boxed_3126_, v___x_3108_, v_params_3109_, v_args_3110_, v_indices_3111_, v___x_16851__boxed_3127_, v___x_3113_, v_a_3114_, v___x_3115_, v___f_3116_, v___x_3117_, v_targetArgs_3118_, v_x_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec_ref(v_x_3119_);
lean_dec_ref(v_targetArgs_3118_);
lean_dec_ref(v_a_3114_);
lean_dec_ref(v_indices_3111_);
lean_dec_ref(v_args_3110_);
lean_dec(v___x_3108_);
lean_dec(v___x_3102_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(lean_object* v___x_3129_, lean_object* v___x_3130_, uint8_t v___x_3131_, lean_object* v___x_3132_, lean_object* v___x_3133_, uint8_t v___x_3134_, lean_object* v___x_3135_, lean_object* v_params_3136_, lean_object* v_args_3137_, uint8_t v___x_3138_, lean_object* v___x_3139_, lean_object* v_a_3140_, lean_object* v___x_3141_, lean_object* v___f_3142_, lean_object* v___x_3143_, lean_object* v___x_3144_, lean_object* v_indices_3145_, lean_object* v_goalType_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___f_3156_; lean_object* v___x_3157_; 
v___x_3152_ = l_Lean_mkAppN(v___x_3129_, v_indices_3145_);
v___x_3153_ = lean_box(v___x_3131_);
v___x_3154_ = lean_box(v___x_3134_);
v___x_3155_ = lean_box(v___x_3138_);
v___f_3156_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___boxed), 23, 16);
lean_closure_set(v___f_3156_, 0, v___x_3130_);
lean_closure_set(v___f_3156_, 1, v___x_3152_);
lean_closure_set(v___f_3156_, 2, v___x_3153_);
lean_closure_set(v___f_3156_, 3, v___x_3132_);
lean_closure_set(v___f_3156_, 4, v___x_3133_);
lean_closure_set(v___f_3156_, 5, v___x_3154_);
lean_closure_set(v___f_3156_, 6, v___x_3135_);
lean_closure_set(v___f_3156_, 7, v_params_3136_);
lean_closure_set(v___f_3156_, 8, v_args_3137_);
lean_closure_set(v___f_3156_, 9, v_indices_3145_);
lean_closure_set(v___f_3156_, 10, v___x_3155_);
lean_closure_set(v___f_3156_, 11, v___x_3139_);
lean_closure_set(v___f_3156_, 12, v_a_3140_);
lean_closure_set(v___f_3156_, 13, v___x_3141_);
lean_closure_set(v___f_3156_, 14, v___f_3142_);
lean_closure_set(v___f_3156_, 15, v___x_3143_);
v___x_3157_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3146_, v___x_3144_, v___f_3156_, v___x_3138_, v___x_3138_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
return v___x_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed(lean_object** _args){
lean_object* v___x_3158_ = _args[0];
lean_object* v___x_3159_ = _args[1];
lean_object* v___x_3160_ = _args[2];
lean_object* v___x_3161_ = _args[3];
lean_object* v___x_3162_ = _args[4];
lean_object* v___x_3163_ = _args[5];
lean_object* v___x_3164_ = _args[6];
lean_object* v_params_3165_ = _args[7];
lean_object* v_args_3166_ = _args[8];
lean_object* v___x_3167_ = _args[9];
lean_object* v___x_3168_ = _args[10];
lean_object* v_a_3169_ = _args[11];
lean_object* v___x_3170_ = _args[12];
lean_object* v___f_3171_ = _args[13];
lean_object* v___x_3172_ = _args[14];
lean_object* v___x_3173_ = _args[15];
lean_object* v_indices_3174_ = _args[16];
lean_object* v_goalType_3175_ = _args[17];
lean_object* v___y_3176_ = _args[18];
lean_object* v___y_3177_ = _args[19];
lean_object* v___y_3178_ = _args[20];
lean_object* v___y_3179_ = _args[21];
lean_object* v___y_3180_ = _args[22];
_start:
{
uint8_t v___x_17182__boxed_3181_; uint8_t v___x_17185__boxed_3182_; uint8_t v___x_17187__boxed_3183_; lean_object* v_res_3184_; 
v___x_17182__boxed_3181_ = lean_unbox(v___x_3160_);
v___x_17185__boxed_3182_ = lean_unbox(v___x_3163_);
v___x_17187__boxed_3183_ = lean_unbox(v___x_3167_);
v_res_3184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4(v___x_3158_, v___x_3159_, v___x_17182__boxed_3181_, v___x_3161_, v___x_3162_, v___x_17185__boxed_3182_, v___x_3164_, v_params_3165_, v_args_3166_, v___x_17187__boxed_3183_, v___x_3168_, v_a_3169_, v___x_3170_, v___f_3171_, v___x_3172_, v___x_3173_, v_indices_3174_, v_goalType_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
lean_dec(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec(v___y_3177_);
lean_dec_ref(v___y_3176_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(lean_object* v___x_3185_, uint8_t v___x_3186_, lean_object* v_snd_3187_, lean_object* v___x_3188_, uint8_t v___x_3189_, lean_object* v___x_3190_, lean_object* v___x_3191_, lean_object* v_a_3192_, lean_object* v___x_3193_, uint8_t v___x_3194_, lean_object* v___x_3195_, lean_object* v___x_3196_, lean_object* v_params_3197_, lean_object* v_args_3198_, lean_object* v___x_3199_, lean_object* v_a_3200_, lean_object* v___x_3201_, lean_object* v___f_3202_, lean_object* v___x_3203_, lean_object* v___x_3204_, lean_object* v_numIndices_3205_, lean_object* v_goalType_3206_, lean_object* v___x_3207_, lean_object* v___x_3208_, lean_object* v_fst_3209_, lean_object* v___x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v_lctx_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v_lctx_3216_ = lean_ctor_get(v___y_3211_, 2);
lean_inc(v___x_3185_);
lean_inc_ref(v_lctx_3216_);
v___x_3217_ = l_Lean_LocalContext_get_x21(v_lctx_3216_, v___x_3185_);
v___x_3218_ = l_Lean_LocalDecl_type(v___x_3217_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = 2;
v___x_3220_ = lean_box(0);
v___x_3221_ = 0;
v___x_3222_ = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set_uint8(v___x_3222_, sizeof(void*)*1, v___x_3219_);
lean_ctor_set_uint8(v___x_3222_, sizeof(void*)*1 + 1, v___x_3186_);
lean_ctor_set_uint8(v___x_3222_, sizeof(void*)*1 + 2, v___x_3221_);
lean_inc_ref(v___x_3188_);
lean_inc(v_snd_3187_);
v___x_3223_ = l_Lean_MVarId_rewrite(v_snd_3187_, v___x_3218_, v___x_3188_, v___x_3186_, v___x_3222_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v_a_3224_; lean_object* v_eNew_3225_; lean_object* v_eqProof_3226_; lean_object* v___x_3227_; lean_object* v___f_3228_; lean_object* v___x_3229_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
lean_inc(v_a_3224_);
lean_dec_ref_known(v___x_3223_, 1);
v_eNew_3225_ = lean_ctor_get(v_a_3224_, 0);
lean_inc_ref(v_eNew_3225_);
v_eqProof_3226_ = lean_ctor_get(v_a_3224_, 1);
lean_inc_ref(v_eqProof_3226_);
lean_dec(v_a_3224_);
lean_inc(v___x_3185_);
v___x_3227_ = l_Lean_mkFVar(v___x_3185_);
lean_inc(v_snd_3187_);
v___f_3228_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__2___boxed), 10, 5);
lean_closure_set(v___f_3228_, 0, v_eqProof_3226_);
lean_closure_set(v___f_3228_, 1, v___x_3227_);
lean_closure_set(v___f_3228_, 2, v_eNew_3225_);
lean_closure_set(v___f_3228_, 3, v_snd_3187_);
lean_closure_set(v___f_3228_, 4, v___x_3185_);
v___x_3229_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3187_, v___f_3228_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___y_3232_; uint8_t v___x_3260_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3229_, 1);
v___x_3260_ = lean_nat_dec_lt(v___x_3207_, v___x_3208_);
if (v___x_3260_ == 0)
{
v___y_3232_ = v_fst_3209_;
goto v___jp_3231_;
}
else
{
lean_object* v_fvarId_3261_; lean_object* v_xs_x27_3262_; lean_object* v___x_3263_; 
v_fvarId_3261_ = lean_ctor_get(v_a_3230_, 0);
v_xs_x27_3262_ = lean_array_fset(v_fst_3209_, v___x_3207_, v___x_3210_);
lean_inc(v_fvarId_3261_);
v___x_3263_ = lean_array_fset(v_xs_x27_3262_, v___x_3207_, v_fvarId_3261_);
v___y_3232_ = v___x_3263_;
goto v___jp_3231_;
}
v___jp_3231_:
{
lean_object* v_mvarId_3233_; lean_object* v___x_3234_; 
v_mvarId_3233_ = lean_ctor_get(v_a_3230_, 1);
lean_inc(v_mvarId_3233_);
lean_dec(v_a_3230_);
v___x_3234_ = l_Lean_MVarId_revert(v_mvarId_3233_, v___y_3232_, v___x_3189_, v___x_3189_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v_snd_3236_; lean_object* v___x_3237_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
lean_inc(v_a_3235_);
lean_dec_ref_known(v___x_3234_, 1);
v_snd_3236_ = lean_ctor_get(v_a_3235_, 1);
lean_inc(v_snd_3236_);
lean_dec(v_a_3235_);
v___x_3237_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__4___redArg(v_snd_3236_, v___x_3190_, v___y_3212_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3250_; 
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v___x_3237_, 0);
lean_dec(v_unused_3251_);
v___x_3239_ = v___x_3237_;
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
else
{
lean_dec(v___x_3237_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___f_3245_; lean_object* v___x_3247_; 
v___x_3241_ = l_Lean_Expr_app___override(v___x_3191_, v_a_3192_);
v___x_3242_ = lean_box(v___x_3194_);
v___x_3243_ = lean_box(v___x_3186_);
v___x_3244_ = lean_box(v___x_3189_);
v___f_3245_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__4___boxed), 23, 16);
lean_closure_set(v___f_3245_, 0, v___x_3241_);
lean_closure_set(v___f_3245_, 1, v___x_3193_);
lean_closure_set(v___f_3245_, 2, v___x_3242_);
lean_closure_set(v___f_3245_, 3, v___x_3195_);
lean_closure_set(v___f_3245_, 4, v___x_3188_);
lean_closure_set(v___f_3245_, 5, v___x_3243_);
lean_closure_set(v___f_3245_, 6, v___x_3196_);
lean_closure_set(v___f_3245_, 7, v_params_3197_);
lean_closure_set(v___f_3245_, 8, v_args_3198_);
lean_closure_set(v___f_3245_, 9, v___x_3244_);
lean_closure_set(v___f_3245_, 10, v___x_3199_);
lean_closure_set(v___f_3245_, 11, v_a_3200_);
lean_closure_set(v___f_3245_, 12, v___x_3201_);
lean_closure_set(v___f_3245_, 13, v___f_3202_);
lean_closure_set(v___f_3245_, 14, v___x_3203_);
lean_closure_set(v___f_3245_, 15, v___x_3204_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set_tag(v___x_3239_, 1);
lean_ctor_set(v___x_3239_, 0, v_numIndices_3205_);
v___x_3247_ = v___x_3239_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_numIndices_3205_);
v___x_3247_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_goalType_3206_, v___x_3247_, v___f_3245_, v___x_3189_, v___x_3189_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec_ref(v___y_3211_);
return v___x_3248_;
}
}
}
else
{
lean_dec_ref(v___y_3211_);
lean_dec_ref(v_goalType_3206_);
lean_dec(v_numIndices_3205_);
lean_dec(v___x_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v___f_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_a_3200_);
lean_dec_ref(v___x_3199_);
lean_dec_ref(v_args_3198_);
lean_dec_ref(v_params_3197_);
lean_dec(v___x_3196_);
lean_dec(v___x_3195_);
lean_dec(v___x_3193_);
lean_dec_ref(v_a_3192_);
lean_dec_ref(v___x_3191_);
lean_dec_ref(v___x_3188_);
return v___x_3237_;
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___y_3211_);
lean_dec_ref(v_goalType_3206_);
lean_dec(v_numIndices_3205_);
lean_dec(v___x_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v___f_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_a_3200_);
lean_dec_ref(v___x_3199_);
lean_dec_ref(v_args_3198_);
lean_dec_ref(v_params_3197_);
lean_dec(v___x_3196_);
lean_dec(v___x_3195_);
lean_dec(v___x_3193_);
lean_dec_ref(v_a_3192_);
lean_dec_ref(v___x_3191_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v___x_3188_);
v_a_3252_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3234_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3234_);
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
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec_ref(v___y_3211_);
lean_dec_ref(v_fst_3209_);
lean_dec_ref(v_goalType_3206_);
lean_dec(v_numIndices_3205_);
lean_dec(v___x_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v___f_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_a_3200_);
lean_dec_ref(v___x_3199_);
lean_dec_ref(v_args_3198_);
lean_dec_ref(v_params_3197_);
lean_dec(v___x_3196_);
lean_dec(v___x_3195_);
lean_dec(v___x_3193_);
lean_dec_ref(v_a_3192_);
lean_dec_ref(v___x_3191_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v___x_3188_);
v_a_3264_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3229_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3229_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
}
else
{
lean_object* v_a_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3279_; 
lean_dec_ref(v___y_3211_);
lean_dec_ref(v_fst_3209_);
lean_dec_ref(v_goalType_3206_);
lean_dec(v_numIndices_3205_);
lean_dec(v___x_3204_);
lean_dec(v___x_3203_);
lean_dec_ref(v___f_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_a_3200_);
lean_dec_ref(v___x_3199_);
lean_dec_ref(v_args_3198_);
lean_dec_ref(v_params_3197_);
lean_dec(v___x_3196_);
lean_dec(v___x_3195_);
lean_dec(v___x_3193_);
lean_dec_ref(v_a_3192_);
lean_dec_ref(v___x_3191_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v___x_3188_);
lean_dec(v_snd_3187_);
lean_dec(v___x_3185_);
v_a_3272_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3279_ == 0)
{
v___x_3274_ = v___x_3223_;
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_a_3272_);
lean_dec(v___x_3223_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3279_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_a_3272_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
return v___x_3277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed(lean_object** _args){
lean_object* v___x_3280_ = _args[0];
lean_object* v___x_3281_ = _args[1];
lean_object* v_snd_3282_ = _args[2];
lean_object* v___x_3283_ = _args[3];
lean_object* v___x_3284_ = _args[4];
lean_object* v___x_3285_ = _args[5];
lean_object* v___x_3286_ = _args[6];
lean_object* v_a_3287_ = _args[7];
lean_object* v___x_3288_ = _args[8];
lean_object* v___x_3289_ = _args[9];
lean_object* v___x_3290_ = _args[10];
lean_object* v___x_3291_ = _args[11];
lean_object* v_params_3292_ = _args[12];
lean_object* v_args_3293_ = _args[13];
lean_object* v___x_3294_ = _args[14];
lean_object* v_a_3295_ = _args[15];
lean_object* v___x_3296_ = _args[16];
lean_object* v___f_3297_ = _args[17];
lean_object* v___x_3298_ = _args[18];
lean_object* v___x_3299_ = _args[19];
lean_object* v_numIndices_3300_ = _args[20];
lean_object* v_goalType_3301_ = _args[21];
lean_object* v___x_3302_ = _args[22];
lean_object* v___x_3303_ = _args[23];
lean_object* v_fst_3304_ = _args[24];
lean_object* v___x_3305_ = _args[25];
lean_object* v___y_3306_ = _args[26];
lean_object* v___y_3307_ = _args[27];
lean_object* v___y_3308_ = _args[28];
lean_object* v___y_3309_ = _args[29];
lean_object* v___y_3310_ = _args[30];
_start:
{
uint8_t v___x_17250__boxed_3311_; uint8_t v___x_17253__boxed_3312_; uint8_t v___x_17258__boxed_3313_; lean_object* v_res_3314_; 
v___x_17250__boxed_3311_ = lean_unbox(v___x_3281_);
v___x_17253__boxed_3312_ = lean_unbox(v___x_3284_);
v___x_17258__boxed_3313_ = lean_unbox(v___x_3289_);
v_res_3314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5(v___x_3280_, v___x_17250__boxed_3311_, v_snd_3282_, v___x_3283_, v___x_17253__boxed_3312_, v___x_3285_, v___x_3286_, v_a_3287_, v___x_3288_, v___x_17258__boxed_3313_, v___x_3290_, v___x_3291_, v_params_3292_, v_args_3293_, v___x_3294_, v_a_3295_, v___x_3296_, v___f_3297_, v___x_3298_, v___x_3299_, v_numIndices_3300_, v_goalType_3301_, v___x_3302_, v___x_3303_, v_fst_3304_, v___x_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
lean_dec(v___y_3309_);
lean_dec_ref(v___y_3308_);
lean_dec(v___y_3307_);
lean_dec(v___x_3303_);
lean_dec(v___x_3302_);
return v_res_3314_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(uint8_t v___x_3315_, lean_object* v_x_3316_){
_start:
{
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1___boxed(lean_object* v___x_3317_, lean_object* v_x_3318_){
_start:
{
uint8_t v___x_17449__boxed_3319_; uint8_t v_res_3320_; lean_object* v_r_3321_; 
v___x_17449__boxed_3319_ = lean_unbox(v___x_3317_);
v_res_3320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__1(v___x_17449__boxed_3319_, v_x_3318_);
lean_dec(v_x_3318_);
v_r_3321_ = lean_box(v_res_3320_);
return v_r_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(lean_object* v___x_3325_, lean_object* v_a_3326_, lean_object* v_numIndices_3327_, lean_object* v___x_3328_, lean_object* v___x_3329_, lean_object* v___x_3330_, lean_object* v___x_3331_, lean_object* v_params_3332_, lean_object* v___x_3333_, lean_object* v_a_3334_, lean_object* v___x_3335_, lean_object* v___x_3336_, lean_object* v___x_3337_, lean_object* v_args_3338_, lean_object* v_goalType_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v___x_3345_; uint8_t v___x_3346_; 
v___x_3345_ = lean_array_get_size(v_args_3338_);
v___x_3346_ = lean_nat_dec_eq(v___x_3345_, v___x_3325_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec_ref(v_goalType_3339_);
lean_dec_ref(v_args_3338_);
lean_dec(v___x_3336_);
lean_dec(v___x_3335_);
lean_dec_ref(v_a_3334_);
lean_dec_ref(v___x_3333_);
lean_dec_ref(v_params_3332_);
lean_dec_ref(v___x_3331_);
lean_dec_ref(v___x_3330_);
lean_dec(v___x_3328_);
lean_dec(v_numIndices_3327_);
lean_dec(v___x_3325_);
v___x_3347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__1);
v___x_3348_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3347_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
return v___x_3348_;
}
else
{
if (lean_obj_tag(v_a_3326_) == 7)
{
lean_object* v_binderType_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_binderType_3349_ = lean_ctor_get(v_a_3326_, 1);
lean_inc_ref(v_binderType_3349_);
v___x_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_binderType_3349_);
v___x_3351_ = 0;
v___x_3352_ = lean_box(0);
v___x_3353_ = l_Lean_Meta_mkFreshExprMVar(v___x_3350_, v___x_3351_, v___x_3352_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v___x_3355_ = l_Lean_Expr_mvarId_x21(v_a_3354_);
v___x_3356_ = lean_nat_add(v_numIndices_3327_, v___x_3325_);
v___x_3357_ = lean_box(0);
v___x_3358_ = 0;
v___x_3359_ = l_Lean_Meta_introNCore(v___x_3355_, v___x_3356_, v___x_3357_, v___x_3358_, v___x_3358_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v_fst_3361_; lean_object* v_snd_3362_; lean_object* v___f_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v_fst_3361_ = lean_ctor_get(v_a_3360_, 0);
lean_inc(v_fst_3361_);
v_snd_3362_ = lean_ctor_get(v_a_3360_, 1);
lean_inc_n(v_snd_3362_, 2);
lean_dec(v_a_3360_);
v___f_3363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___closed__0));
v___x_3364_ = lean_array_fget(v_args_3338_, v___x_3328_);
v___x_3365_ = lean_array_get_size(v_fst_3361_);
v___x_3366_ = lean_nat_sub(v___x_3365_, v___x_3325_);
v___x_3367_ = lean_array_get(v___x_3329_, v_fst_3361_, v___x_3366_);
v___x_3368_ = lean_box(v___x_3346_);
v___x_3369_ = lean_box(v___x_3358_);
v___x_3370_ = lean_box(v___x_3351_);
v___f_3371_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__5___boxed), 31, 26);
lean_closure_set(v___f_3371_, 0, v___x_3367_);
lean_closure_set(v___f_3371_, 1, v___x_3368_);
lean_closure_set(v___f_3371_, 2, v_snd_3362_);
lean_closure_set(v___f_3371_, 3, v___x_3330_);
lean_closure_set(v___f_3371_, 4, v___x_3369_);
lean_closure_set(v___f_3371_, 5, v___x_3364_);
lean_closure_set(v___f_3371_, 6, v___x_3331_);
lean_closure_set(v___f_3371_, 7, v_a_3354_);
lean_closure_set(v___f_3371_, 8, v___x_3325_);
lean_closure_set(v___f_3371_, 9, v___x_3370_);
lean_closure_set(v___f_3371_, 10, v___x_3352_);
lean_closure_set(v___f_3371_, 11, v___x_3328_);
lean_closure_set(v___f_3371_, 12, v_params_3332_);
lean_closure_set(v___f_3371_, 13, v_args_3338_);
lean_closure_set(v___f_3371_, 14, v___x_3333_);
lean_closure_set(v___f_3371_, 15, v_a_3334_);
lean_closure_set(v___f_3371_, 16, v___x_3335_);
lean_closure_set(v___f_3371_, 17, v___f_3363_);
lean_closure_set(v___f_3371_, 18, v___x_3357_);
lean_closure_set(v___f_3371_, 19, v___x_3336_);
lean_closure_set(v___f_3371_, 20, v_numIndices_3327_);
lean_closure_set(v___f_3371_, 21, v_goalType_3339_);
lean_closure_set(v___f_3371_, 22, v___x_3366_);
lean_closure_set(v___f_3371_, 23, v___x_3365_);
lean_closure_set(v___f_3371_, 24, v_fst_3361_);
lean_closure_set(v___f_3371_, 25, v___x_3337_);
v___x_3372_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__4___redArg(v_snd_3362_, v___f_3371_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
return v___x_3372_;
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v_a_3354_);
lean_dec_ref(v_goalType_3339_);
lean_dec_ref(v_args_3338_);
lean_dec(v___x_3336_);
lean_dec(v___x_3335_);
lean_dec_ref(v_a_3334_);
lean_dec_ref(v___x_3333_);
lean_dec_ref(v_params_3332_);
lean_dec_ref(v___x_3331_);
lean_dec_ref(v___x_3330_);
lean_dec(v___x_3328_);
lean_dec(v_numIndices_3327_);
lean_dec(v___x_3325_);
v_a_3373_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3359_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3359_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec_ref(v_goalType_3339_);
lean_dec_ref(v_args_3338_);
lean_dec(v___x_3336_);
lean_dec(v___x_3335_);
lean_dec_ref(v_a_3334_);
lean_dec_ref(v___x_3333_);
lean_dec_ref(v_params_3332_);
lean_dec_ref(v___x_3331_);
lean_dec_ref(v___x_3330_);
lean_dec(v___x_3328_);
lean_dec(v_numIndices_3327_);
lean_dec(v___x_3325_);
v_a_3381_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3353_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3353_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
lean_dec_ref(v_goalType_3339_);
lean_dec_ref(v_args_3338_);
lean_dec(v___x_3336_);
lean_dec(v___x_3335_);
lean_dec_ref(v_a_3334_);
lean_dec_ref(v___x_3333_);
lean_dec_ref(v_params_3332_);
lean_dec_ref(v___x_3331_);
lean_dec_ref(v___x_3330_);
lean_dec(v___x_3328_);
lean_dec(v_numIndices_3327_);
lean_dec(v___x_3325_);
v___x_3389_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__3___closed__10);
v___x_3390_ = l_Lean_throwError___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__1___redArg(v___x_3389_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
return v___x_3390_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed(lean_object** _args){
lean_object* v___x_3391_ = _args[0];
lean_object* v_a_3392_ = _args[1];
lean_object* v_numIndices_3393_ = _args[2];
lean_object* v___x_3394_ = _args[3];
lean_object* v___x_3395_ = _args[4];
lean_object* v___x_3396_ = _args[5];
lean_object* v___x_3397_ = _args[6];
lean_object* v_params_3398_ = _args[7];
lean_object* v___x_3399_ = _args[8];
lean_object* v_a_3400_ = _args[9];
lean_object* v___x_3401_ = _args[10];
lean_object* v___x_3402_ = _args[11];
lean_object* v___x_3403_ = _args[12];
lean_object* v_args_3404_ = _args[13];
lean_object* v_goalType_3405_ = _args[14];
lean_object* v___y_3406_ = _args[15];
lean_object* v___y_3407_ = _args[16];
lean_object* v___y_3408_ = _args[17];
lean_object* v___y_3409_ = _args[18];
lean_object* v___y_3410_ = _args[19];
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6(v___x_3391_, v_a_3392_, v_numIndices_3393_, v___x_3394_, v___x_3395_, v___x_3396_, v___x_3397_, v_params_3398_, v___x_3399_, v_a_3400_, v___x_3401_, v___x_3402_, v___x_3403_, v_args_3404_, v_goalType_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___x_3395_);
lean_dec_ref(v_a_3392_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(lean_object* v_constName_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___x_3418_; lean_object* v_env_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; 
v___x_3418_ = lean_st_ref_get(v___y_3416_);
v_env_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc_ref(v_env_3419_);
lean_dec(v___x_3418_);
v___x_3420_ = 0;
lean_inc(v_constName_3412_);
v___x_3421_ = l_Lean_Environment_findConstVal_x3f(v_env_3419_, v_constName_3412_, v___x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
return v___x_3422_;
}
else
{
lean_object* v_val_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec(v_constName_3412_);
v_val_3423_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3421_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_val_3423_);
lean_dec(v___x_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 0);
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_val_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4___boxed(lean_object* v_constName_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(lean_object* v_constName_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v___x_3444_; 
lean_inc(v_constName_3438_);
v___x_3444_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3_spec__4(v_constName_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3456_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3456_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3456_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v_levelParams_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3454_; 
v_levelParams_3449_ = lean_ctor_get(v_a_3445_, 1);
lean_inc(v_levelParams_3449_);
lean_dec(v_a_3445_);
v___x_3450_ = lean_box(0);
v___x_3451_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3449_, v___x_3450_);
v___x_3452_ = l_Lean_mkConst(v_constName_3438_, v___x_3451_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3452_);
v___x_3454_ = v___x_3447_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
else
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
lean_dec(v_constName_3438_);
v_a_3457_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3444_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3444_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3___boxed(lean_object* v_constName_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v_res_3471_; 
v_res_3471_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v_constName_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(lean_object* v_levels_3474_, lean_object* v_params_3475_, lean_object* v___y_3476_, lean_object* v_predicates_3477_, lean_object* v_as_3478_, size_t v_sz_3479_, size_t v_i_3480_, lean_object* v_b_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_lt(v_i_3480_, v_sz_3479_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_params_3475_);
lean_dec(v_levels_3474_);
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_b_3481_);
return v___x_3488_;
}
else
{
lean_object* v_a_3489_; lean_object* v_toConstantVal_3490_; lean_object* v_numParams_3491_; lean_object* v_numIndices_3492_; lean_object* v_name_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_a_3489_ = lean_array_uget_borrowed(v_as_3478_, v_i_3480_);
v_toConstantVal_3490_ = lean_ctor_get(v_a_3489_, 0);
v_numParams_3491_ = lean_ctor_get(v_a_3489_, 1);
v_numIndices_3492_ = lean_ctor_get(v_a_3489_, 2);
v_name_3493_ = lean_ctor_get(v_toConstantVal_3490_, 0);
lean_inc(v_name_3493_);
v___x_3494_ = l_Lean_mkCasesOnName(v_name_3493_);
lean_inc(v___x_3494_);
v___x_3495_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2(v___x_3494_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v___x_3497_; 
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc(v_a_3496_);
lean_dec_ref_known(v___x_3495_, 1);
v___x_3497_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__3(v___x_3494_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
lean_inc_ref(v_params_3475_);
v___x_3499_ = l_Array_append___redArg(v_params_3475_, v_predicates_3477_);
v___x_3500_ = l_Lean_mkAppN(v_a_3498_, v___x_3499_);
lean_dec_ref(v___x_3499_);
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3484_);
lean_inc(v___y_3483_);
lean_inc_ref(v___y_3482_);
lean_inc_ref(v___x_3500_);
v___x_3501_ = lean_infer_type(v___x_3500_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; lean_object* v___x_3503_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
lean_dec_ref_known(v___x_3501_, 1);
lean_inc(v___y_3485_);
lean_inc_ref(v___y_3484_);
lean_inc(v___y_3483_);
lean_inc_ref(v___y_3482_);
lean_inc_ref(v___x_3500_);
v___x_3503_ = lean_infer_type(v___x_3500_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; uint8_t v___x_3517_; lean_object* v___x_3518_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = lean_unsigned_to_nat(0u);
v___x_3506_ = lean_box(0);
v___x_3507_ = lean_box(0);
lean_inc_ref(v___y_3476_);
lean_inc_ref_n(v_params_3475_, 2);
lean_inc_n(v_levels_3474_, 2);
lean_inc_n(v_name_3493_, 2);
lean_inc(v_numParams_3491_);
v___f_3508_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3508_, 0, v_numParams_3491_);
lean_closure_set(v___f_3508_, 1, v_name_3493_);
lean_closure_set(v___f_3508_, 2, v_levels_3474_);
lean_closure_set(v___f_3508_, 3, v_params_3475_);
lean_closure_set(v___f_3508_, 4, v___y_3476_);
lean_closure_set(v___f_3508_, 5, v___x_3505_);
v___x_3509_ = lean_replace_expr(v___f_3508_, v_a_3502_);
lean_dec(v_a_3502_);
lean_dec_ref(v___f_3508_);
v___x_3510_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3493_);
v___x_3511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__1));
lean_inc(v___x_3510_);
v___x_3512_ = l_Lean_Name_append(v___x_3510_, v___x_3511_);
v___x_3513_ = l_Lean_mkConst(v___x_3512_, v_levels_3474_);
v___x_3514_ = lean_unsigned_to_nat(1u);
v___x_3515_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___closed__0));
lean_inc_ref(v___x_3509_);
lean_inc(v_numIndices_3492_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___lam__6___boxed), 20, 13);
lean_closure_set(v___f_3516_, 0, v___x_3514_);
lean_closure_set(v___f_3516_, 1, v_a_3504_);
lean_closure_set(v___f_3516_, 2, v_numIndices_3492_);
lean_closure_set(v___f_3516_, 3, v___x_3505_);
lean_closure_set(v___f_3516_, 4, v___x_3506_);
lean_closure_set(v___f_3516_, 5, v___x_3513_);
lean_closure_set(v___f_3516_, 6, v___x_3500_);
lean_closure_set(v___f_3516_, 7, v_params_3475_);
lean_closure_set(v___f_3516_, 8, v___x_3509_);
lean_closure_set(v___f_3516_, 9, v_a_3496_);
lean_closure_set(v___f_3516_, 10, v___x_3510_);
lean_closure_set(v___f_3516_, 11, v___x_3515_);
lean_closure_set(v___f_3516_, 12, v___x_3507_);
v___x_3517_ = 0;
v___x_3518_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v___x_3509_, v___x_3515_, v___f_3516_, v___x_3517_, v___x_3517_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
if (lean_obj_tag(v___x_3518_) == 0)
{
size_t v___x_3519_; size_t v___x_3520_; 
lean_dec_ref_known(v___x_3518_, 1);
v___x_3519_ = ((size_t)1ULL);
v___x_3520_ = lean_usize_add(v_i_3480_, v___x_3519_);
v_i_3480_ = v___x_3520_;
v_b_3481_ = v___x_3507_;
goto _start;
}
else
{
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_params_3475_);
lean_dec(v_levels_3474_);
return v___x_3518_;
}
}
else
{
lean_object* v_a_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3529_; 
lean_dec(v_a_3502_);
lean_dec_ref(v___x_3500_);
lean_dec(v_a_3496_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_params_3475_);
lean_dec(v_levels_3474_);
v_a_3522_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3529_ == 0)
{
v___x_3524_ = v___x_3503_;
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_a_3522_);
lean_dec(v___x_3503_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3529_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3527_; 
if (v_isShared_3525_ == 0)
{
v___x_3527_ = v___x_3524_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_a_3522_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec_ref(v___x_3500_);
lean_dec(v_a_3496_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_params_3475_);
lean_dec(v_levels_3474_);
v_a_3530_ = lean_ctor_get(v___x_3501_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3501_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3501_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_a_3496_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_params_3475_);
lean_dec(v_levels_3474_);
v_a_3538_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3497_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3497_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v___x_3494_);
lean_dec_ref(v___y_3476_);
lean_dec_ref(v_params_3475_);
lean_dec(v_levels_3474_);
v_a_3546_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3495_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3495_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6___boxed(lean_object* v_levels_3554_, lean_object* v_params_3555_, lean_object* v___y_3556_, lean_object* v_predicates_3557_, lean_object* v_as_3558_, lean_object* v_sz_3559_, lean_object* v_i_3560_, lean_object* v_b_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
size_t v_sz_boxed_3567_; size_t v_i_boxed_3568_; lean_object* v_res_3569_; 
v_sz_boxed_3567_ = lean_unbox_usize(v_sz_3559_);
lean_dec(v_sz_3559_);
v_i_boxed_3568_ = lean_unbox_usize(v_i_3560_);
lean_dec(v_i_3560_);
v_res_3569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3554_, v_params_3555_, v___y_3556_, v_predicates_3557_, v_as_3558_, v_sz_boxed_3567_, v_i_boxed_3568_, v_b_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec_ref(v_as_3558_);
lean_dec_ref(v_predicates_3557_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(lean_object* v_levels_3570_, size_t v_sz_3571_, size_t v_i_3572_, lean_object* v_bs_3573_){
_start:
{
uint8_t v___x_3574_; 
v___x_3574_ = lean_usize_dec_lt(v_i_3572_, v_sz_3571_);
if (v___x_3574_ == 0)
{
lean_dec(v_levels_3570_);
return v_bs_3573_;
}
else
{
lean_object* v_v_3575_; lean_object* v_toConstantVal_3576_; lean_object* v_name_3577_; lean_object* v___x_3578_; lean_object* v_bs_x27_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; size_t v___x_3582_; size_t v___x_3583_; lean_object* v___x_3584_; 
v_v_3575_ = lean_array_uget_borrowed(v_bs_3573_, v_i_3572_);
v_toConstantVal_3576_ = lean_ctor_get(v_v_3575_, 0);
v_name_3577_ = lean_ctor_get(v_toConstantVal_3576_, 0);
lean_inc(v_name_3577_);
v___x_3578_ = lean_unsigned_to_nat(0u);
v_bs_x27_3579_ = lean_array_uset(v_bs_3573_, v_i_3572_, v___x_3578_);
v___x_3580_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_3577_);
lean_inc(v_levels_3570_);
v___x_3581_ = l_Lean_mkConst(v___x_3580_, v_levels_3570_);
v___x_3582_ = ((size_t)1ULL);
v___x_3583_ = lean_usize_add(v_i_3572_, v___x_3582_);
v___x_3584_ = lean_array_uset(v_bs_x27_3579_, v_i_3572_, v___x_3581_);
v_i_3572_ = v___x_3583_;
v_bs_3573_ = v___x_3584_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0___boxed(lean_object* v_levels_3586_, lean_object* v_sz_3587_, lean_object* v_i_3588_, lean_object* v_bs_3589_){
_start:
{
size_t v_sz_boxed_3590_; size_t v_i_boxed_3591_; lean_object* v_res_3592_; 
v_sz_boxed_3590_ = lean_unbox_usize(v_sz_3587_);
lean_dec(v_sz_3587_);
v_i_boxed_3591_ = lean_unbox_usize(v_i_3588_);
lean_dec(v_i_3588_);
v_res_3592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3586_, v_sz_boxed_3590_, v_i_boxed_3591_, v_bs_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(lean_object* v_infos_3593_, lean_object* v_levels_3594_, lean_object* v___y_3595_, lean_object* v_params_3596_, lean_object* v_x_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
size_t v_sz_3603_; size_t v___x_3604_; lean_object* v_predicates_3605_; size_t v_sz_3606_; lean_object* v_predicates_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_sz_3603_ = lean_array_size(v_infos_3593_);
v___x_3604_ = ((size_t)0ULL);
lean_inc_ref(v_infos_3593_);
lean_inc(v_levels_3594_);
v_predicates_3605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__0(v_levels_3594_, v_sz_3603_, v___x_3604_, v_infos_3593_);
v_sz_3606_ = lean_array_size(v_predicates_3605_);
v_predicates_3607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3596_, v_sz_3606_, v___x_3604_, v_predicates_3605_);
v___x_3608_ = lean_box(0);
v___x_3609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__6(v_levels_3594_, v_params_3596_, v___y_3595_, v_predicates_3607_, v_infos_3593_, v_sz_3603_, v___x_3604_, v___x_3608_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec_ref(v_infos_3593_);
lean_dec_ref(v_predicates_3607_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v___x_3609_, 0);
lean_dec(v_unused_3617_);
v___x_3611_ = v___x_3609_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_dec(v___x_3609_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 0, v___x_3608_);
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3608_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
else
{
return v___x_3609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed(lean_object* v_infos_3618_, lean_object* v_levels_3619_, lean_object* v___y_3620_, lean_object* v_params_3621_, lean_object* v_x_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0(v_infos_3618_, v_levels_3619_, v___y_3620_, v_params_3621_, v_x_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec_ref(v_x_3622_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(lean_object* v_as_3629_, size_t v_i_3630_, size_t v_stop_3631_, lean_object* v_b_3632_){
_start:
{
uint8_t v___x_3633_; 
v___x_3633_ = lean_usize_dec_eq(v_i_3630_, v_stop_3631_);
if (v___x_3633_ == 0)
{
lean_object* v___x_3634_; lean_object* v_ctors_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; size_t v___x_3638_; size_t v___x_3639_; 
v___x_3634_ = lean_array_uget_borrowed(v_as_3629_, v_i_3630_);
v_ctors_3635_ = lean_ctor_get(v___x_3634_, 4);
lean_inc(v_ctors_3635_);
v___x_3636_ = lean_array_mk(v_ctors_3635_);
v___x_3637_ = l_Array_append___redArg(v_b_3632_, v___x_3636_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = ((size_t)1ULL);
v___x_3639_ = lean_usize_add(v_i_3630_, v___x_3638_);
v_i_3630_ = v___x_3639_;
v_b_3632_ = v___x_3637_;
goto _start;
}
else
{
return v_b_3632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7___boxed(lean_object* v_as_3641_, lean_object* v_i_3642_, lean_object* v_stop_3643_, lean_object* v_b_3644_){
_start:
{
size_t v_i_boxed_3645_; size_t v_stop_boxed_3646_; lean_object* v_res_3647_; 
v_i_boxed_3645_ = lean_unbox_usize(v_i_3642_);
lean_dec(v_i_3642_);
v_stop_boxed_3646_ = lean_unbox_usize(v_stop_3643_);
lean_dec(v_stop_3643_);
v_res_3647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_as_3641_, v_i_boxed_3645_, v_stop_boxed_3646_, v_b_3644_);
lean_dec_ref(v_as_3641_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(lean_object* v_infos_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v_toConstantVal_3659_; lean_object* v_numParams_3660_; lean_object* v_levelParams_3661_; lean_object* v_type_3662_; lean_object* v___x_3663_; lean_object* v_levels_3664_; lean_object* v___y_3666_; lean_object* v___x_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; 
v___x_3656_ = l_Lean_instInhabitedInductiveVal_default;
v___x_3657_ = lean_unsigned_to_nat(0u);
v___x_3658_ = lean_array_get_borrowed(v___x_3656_, v_infos_3650_, v___x_3657_);
v_toConstantVal_3659_ = lean_ctor_get(v___x_3658_, 0);
v_numParams_3660_ = lean_ctor_get(v___x_3658_, 1);
lean_inc(v_numParams_3660_);
v_levelParams_3661_ = lean_ctor_get(v_toConstantVal_3659_, 1);
v_type_3662_ = lean_ctor_get(v_toConstantVal_3659_, 2);
lean_inc_ref(v_type_3662_);
v___x_3663_ = lean_box(0);
lean_inc(v_levelParams_3661_);
v_levels_3664_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_3661_, v___x_3663_);
v___x_3673_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___closed__0));
v___x_3674_ = lean_array_get_size(v_infos_3650_);
v___x_3675_ = lean_nat_dec_lt(v___x_3657_, v___x_3674_);
if (v___x_3675_ == 0)
{
v___y_3666_ = v___x_3673_;
goto v___jp_3665_;
}
else
{
uint8_t v___x_3676_; 
v___x_3676_ = lean_nat_dec_le(v___x_3674_, v___x_3674_);
if (v___x_3676_ == 0)
{
if (v___x_3675_ == 0)
{
v___y_3666_ = v___x_3673_;
goto v___jp_3665_;
}
else
{
size_t v___x_3677_; size_t v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = ((size_t)0ULL);
v___x_3678_ = lean_usize_of_nat(v___x_3674_);
v___x_3679_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3650_, v___x_3677_, v___x_3678_, v___x_3673_);
v___y_3666_ = v___x_3679_;
goto v___jp_3665_;
}
}
else
{
size_t v___x_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = ((size_t)0ULL);
v___x_3681_ = lean_usize_of_nat(v___x_3674_);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__7(v_infos_3650_, v___x_3680_, v___x_3681_, v___x_3673_);
v___y_3666_ = v___x_3682_;
goto v___jp_3665_;
}
}
v___jp_3665_:
{
lean_object* v___f_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; lean_object* v___x_3672_; 
lean_inc_ref(v_infos_3650_);
v___f_3667_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3667_, 0, v_infos_3650_);
lean_closure_set(v___f_3667_, 1, v_levels_3664_);
lean_closure_set(v___f_3667_, 2, v___y_3666_);
v___x_3668_ = lean_array_get_size(v_infos_3650_);
lean_dec_ref(v_infos_3650_);
v___x_3669_ = lean_nat_sub(v_numParams_3660_, v___x_3668_);
lean_dec(v_numParams_3660_);
v___x_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
v___x_3671_ = 0;
v___x_3672_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__5___redArg(v_type_3662_, v___x_3670_, v___f_3667_, v___x_3671_, v___x_3671_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
return v___x_3672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive___boxed(lean_object* v_infos_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_infos_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(lean_object* v_00_u03b1_3690_, lean_object* v_constName_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___redArg(v_constName_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2___boxed(lean_object* v_00_u03b1_3698_, lean_object* v_constName_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2(v_00_u03b1_3698_, v_constName_3699_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(lean_object* v_00_u03b1_3706_, lean_object* v_ref_3707_, lean_object* v_constName_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v___x_3714_; 
v___x_3714_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___redArg(v_ref_3707_, v_constName_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5___boxed(lean_object* v_00_u03b1_3715_, lean_object* v_ref_3716_, lean_object* v_constName_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
lean_object* v_res_3723_; 
v_res_3723_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5(v_00_u03b1_3715_, v_ref_3716_, v_constName_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v_ref_3716_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(lean_object* v_00_u03b1_3724_, lean_object* v_ref_3725_, lean_object* v_msg_3726_, lean_object* v_declHint_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___redArg(v_ref_3725_, v_msg_3726_, v_declHint_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b1_3734_, lean_object* v_ref_3735_, lean_object* v_msg_3736_, lean_object* v_declHint_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v_res_3743_; 
v_res_3743_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9(v_00_u03b1_3734_, v_ref_3735_, v_msg_3736_, v_declHint_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
lean_dec(v___y_3741_);
lean_dec_ref(v___y_3740_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
lean_dec(v_ref_3735_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(lean_object* v_msg_3744_, lean_object* v_declHint_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; 
v___x_3751_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___redArg(v_msg_3744_, v_declHint_3745_, v___y_3749_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_3752_, lean_object* v_declHint_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v_res_3759_; 
v_res_3759_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__11_spec__12(v_msg_3752_, v_declHint_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(lean_object* v_00_u03b1_3760_, lean_object* v_ref_3761_, lean_object* v_msg_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___redArg(v_ref_3761_, v_msg_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12___boxed(lean_object* v_00_u03b1_3769_, lean_object* v_ref_3770_, lean_object* v_msg_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive_spec__2_spec__2_spec__5_spec__9_spec__12(v_00_u03b1_3769_, v_ref_3770_, v_msg_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_);
lean_dec(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v_ref_3770_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(lean_object* v___x_3781_, lean_object* v___x_3782_, lean_object* v_params_3783_, size_t v_sz_3784_, size_t v_i_3785_, lean_object* v_bs_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v___x_3792_; 
v___x_3792_ = lean_usize_dec_lt(v_i_3785_, v_sz_3784_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; 
lean_dec_ref(v_params_3783_);
lean_dec_ref(v___x_3782_);
lean_dec(v___x_3781_);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_bs_3786_);
return v___x_3793_;
}
else
{
lean_object* v_v_3794_; lean_object* v_toConstantVal_3795_; lean_object* v_name_3796_; lean_object* v___x_3797_; lean_object* v_bs_x27_3798_; lean_object* v___y_3800_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v_v_3794_ = lean_array_uget_borrowed(v_bs_3786_, v_i_3785_);
v_toConstantVal_3795_ = lean_ctor_get(v_v_3794_, 0);
v_name_3796_ = lean_ctor_get(v_toConstantVal_3795_, 0);
lean_inc(v_name_3796_);
v___x_3797_ = lean_unsigned_to_nat(0u);
v_bs_x27_3798_ = lean_array_uset(v_bs_3786_, v_i_3785_, v___x_3797_);
v___x_3814_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___closed__1));
v___x_3815_ = l_Lean_Name_append(v_name_3796_, v___x_3814_);
lean_inc(v___x_3781_);
v___x_3816_ = l_Lean_mkConst(v___x_3815_, v___x_3781_);
v___x_3817_ = l_Lean_Meta_unfoldDefinition(v___x_3816_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; size_t v_sz_3819_; size_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
v_sz_3819_ = lean_array_size(v___x_3782_);
v___x_3820_ = ((size_t)0ULL);
lean_inc_ref(v___x_3782_);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__2(v_params_3783_, v_sz_3819_, v___x_3820_, v___x_3782_);
lean_inc_ref(v_params_3783_);
v___x_3822_ = l_Array_append___redArg(v_params_3783_, v___x_3821_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = l_Lean_mkAppN(v_a_3818_, v___x_3822_);
lean_dec_ref(v___x_3822_);
v___x_3824_ = 0;
v___x_3825_ = 1;
v___x_3826_ = l_Lean_Meta_mkLambdaFVars(v_params_3783_, v___x_3823_, v___x_3824_, v___x_3792_, v___x_3824_, v___x_3792_, v___x_3825_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
v___y_3800_ = v___x_3826_;
goto v___jp_3799_;
}
else
{
v___y_3800_ = v___x_3817_;
goto v___jp_3799_;
}
v___jp_3799_:
{
if (lean_obj_tag(v___y_3800_) == 0)
{
lean_object* v_a_3801_; size_t v___x_3802_; size_t v___x_3803_; lean_object* v___x_3804_; 
v_a_3801_ = lean_ctor_get(v___y_3800_, 0);
lean_inc(v_a_3801_);
lean_dec_ref_known(v___y_3800_, 1);
v___x_3802_ = ((size_t)1ULL);
v___x_3803_ = lean_usize_add(v_i_3785_, v___x_3802_);
v___x_3804_ = lean_array_uset(v_bs_x27_3798_, v_i_3785_, v_a_3801_);
v_i_3785_ = v___x_3803_;
v_bs_3786_ = v___x_3804_;
goto _start;
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_bs_x27_3798_);
lean_dec_ref(v_params_3783_);
lean_dec_ref(v___x_3782_);
lean_dec(v___x_3781_);
v_a_3806_ = lean_ctor_get(v___y_3800_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___y_3800_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___y_3800_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___y_3800_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg___boxed(lean_object* v___x_3827_, lean_object* v___x_3828_, lean_object* v_params_3829_, lean_object* v_sz_3830_, lean_object* v_i_3831_, lean_object* v_bs_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
size_t v_sz_boxed_3838_; size_t v_i_boxed_3839_; lean_object* v_res_3840_; 
v_sz_boxed_3838_ = lean_unbox_usize(v_sz_3830_);
lean_dec(v_sz_3830_);
v_i_boxed_3839_ = lean_unbox_usize(v_i_3831_);
lean_dec(v_i_3831_);
v_res_3840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3827_, v___x_3828_, v_params_3829_, v_sz_boxed_3838_, v_i_boxed_3839_, v_bs_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0(lean_object* v___x_3841_, lean_object* v___x_3842_, size_t v_sz_3843_, size_t v___x_3844_, lean_object* v_a_3845_, lean_object* v_params_3846_, lean_object* v_x_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_3841_, v___x_3842_, v_params_3846_, v_sz_3843_, v___x_3844_, v_a_3845_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___lam__0___boxed(lean_object* v___x_3856_, lean_object* v___x_3857_, lean_object* v_sz_3858_, lean_object* v___x_3859_, lean_object* v_a_3860_, lean_object* v_params_3861_, lean_object* v_x_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
size_t v_sz_boxed_3870_; size_t v___x_5853__boxed_3871_; lean_object* v_res_3872_; 
v_sz_boxed_3870_ = lean_unbox_usize(v_sz_3858_);
lean_dec(v_sz_3858_);
v___x_5853__boxed_3871_ = lean_unbox_usize(v___x_3859_);
lean_dec(v___x_3859_);
v_res_3872_ = l_Lean_Elab_Command_elabCoinductive___lam__0(v___x_3856_, v___x_3857_, v_sz_boxed_3870_, v___x_5853__boxed_3871_, v_a_3860_, v_params_3861_, v_x_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_, v___y_3868_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec_ref(v_x_3862_);
return v_res_3872_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(lean_object* v___x_3873_, uint8_t v___x_3874_, lean_object* v_attr_3875_){
_start:
{
lean_object* v_name_3876_; lean_object* v___x_3877_; 
v_name_3876_ = lean_ctor_get(v_attr_3875_, 0);
lean_inc(v_name_3876_);
lean_dec_ref(v_attr_3875_);
v___x_3877_ = l_Lean_getAttributeImpl(v___x_3873_, v_name_3876_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_dec_ref_known(v___x_3877_, 1);
return v___x_3874_;
}
else
{
lean_object* v_a_3878_; lean_object* v_toAttributeImplCore_3879_; uint8_t v_applicationTime_3880_; uint8_t v___x_3881_; uint8_t v___x_3882_; uint8_t v___x_3883_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v_toAttributeImplCore_3879_ = lean_ctor_get(v_a_3878_, 0);
lean_inc_ref(v_toAttributeImplCore_3879_);
lean_dec(v_a_3878_);
v_applicationTime_3880_ = lean_ctor_get_uint8(v_toAttributeImplCore_3879_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_3879_);
v___x_3881_ = 1;
v___x_3882_ = l_Lean_instBEqAttributeApplicationTime_beq(v_applicationTime_3880_, v___x_3881_);
v___x_3883_ = lean_bool_not(v___x_3882_);
return v___x_3883_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed(lean_object* v___x_3884_, lean_object* v___x_3885_, lean_object* v_attr_3886_){
_start:
{
uint8_t v___x_5890__boxed_3887_; uint8_t v_res_3888_; lean_object* v_r_3889_; 
v___x_5890__boxed_3887_ = lean_unbox(v___x_3885_);
v_res_3888_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0(v___x_3884_, v___x_5890__boxed_3887_, v_attr_3886_);
v_r_3889_ = lean_box(v_res_3888_);
return v_r_3889_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = l_Lean_instInhabitedExpr;
v___x_3891_ = lean_box(0);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v___x_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(lean_object* v_coinductiveElabData_3893_, lean_object* v___x_3894_, lean_object* v_a_3895_, lean_object* v___x_3896_, size_t v_sz_3897_, size_t v_i_3898_, lean_object* v_bs_3899_){
_start:
{
uint8_t v___x_3900_; 
v___x_3900_ = lean_usize_dec_lt(v_i_3898_, v_sz_3897_);
if (v___x_3900_ == 0)
{
lean_dec(v___x_3896_);
lean_dec_ref(v___x_3894_);
return v_bs_3899_;
}
else
{
lean_object* v___x_3901_; lean_object* v_v_3902_; lean_object* v___x_3903_; lean_object* v_bs_x27_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v_modifiers_3907_; lean_object* v_ref_3908_; uint8_t v_isGreatest_3909_; lean_object* v_stx_3910_; uint8_t v_visibility_3911_; uint8_t v_isProtected_3912_; uint8_t v_computeKind_3913_; uint8_t v_recKind_3914_; uint8_t v_isUnsafe_3915_; lean_object* v_attrs_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3944_; 
v___x_3901_ = l_Lean_Elab_Command_instInhabitedCoinductiveElabData_default;
v_v_3902_ = lean_array_uget(v_bs_3899_, v_i_3898_);
v___x_3903_ = lean_unsigned_to_nat(0u);
v_bs_x27_3904_ = lean_array_uset(v_bs_3899_, v_i_3898_, v___x_3903_);
v___x_3905_ = lean_usize_to_nat(v_i_3898_);
v___x_3906_ = lean_array_get_borrowed(v___x_3901_, v_coinductiveElabData_3893_, v___x_3905_);
v_modifiers_3907_ = lean_ctor_get(v___x_3906_, 3);
lean_inc_ref(v_modifiers_3907_);
v_ref_3908_ = lean_ctor_get(v___x_3906_, 2);
v_isGreatest_3909_ = lean_ctor_get_uint8(v___x_3906_, sizeof(void*)*5);
v_stx_3910_ = lean_ctor_get(v_modifiers_3907_, 0);
v_visibility_3911_ = lean_ctor_get_uint8(v_modifiers_3907_, sizeof(void*)*3);
v_isProtected_3912_ = lean_ctor_get_uint8(v_modifiers_3907_, sizeof(void*)*3 + 1);
v_computeKind_3913_ = lean_ctor_get_uint8(v_modifiers_3907_, sizeof(void*)*3 + 2);
v_recKind_3914_ = lean_ctor_get_uint8(v_modifiers_3907_, sizeof(void*)*3 + 3);
v_isUnsafe_3915_ = lean_ctor_get_uint8(v_modifiers_3907_, sizeof(void*)*3 + 4);
v_attrs_3916_ = lean_ctor_get(v_modifiers_3907_, 2);
v_isSharedCheck_3944_ = !lean_is_exclusive(v_modifiers_3907_);
if (v_isSharedCheck_3944_ == 0)
{
lean_object* v_unused_3945_; 
v_unused_3945_ = lean_ctor_get(v_modifiers_3907_, 1);
lean_dec(v_unused_3945_);
v___x_3918_ = v_modifiers_3907_;
v_isShared_3919_ = v_isSharedCheck_3944_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_attrs_3916_);
lean_inc(v_stx_3910_);
lean_dec(v_modifiers_3907_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3944_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v_fst_3922_; lean_object* v_snd_3923_; lean_object* v___x_3924_; lean_object* v___f_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___closed__0);
v___x_3921_ = lean_array_get_borrowed(v___x_3920_, v_a_3895_, v___x_3905_);
lean_dec(v___x_3905_);
v_fst_3922_ = lean_ctor_get(v___x_3921_, 0);
v_snd_3923_ = lean_ctor_get(v___x_3921_, 1);
v___x_3924_ = lean_box(v___x_3900_);
lean_inc_ref(v___x_3894_);
v___f_3925_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3925_, 0, v___x_3894_);
lean_closure_set(v___f_3925_, 1, v___x_3924_);
v___x_3926_ = lean_box(0);
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v___x_3926_);
v___x_3928_ = v___x_3918_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_stx_3910_);
lean_ctor_set(v_reuseFailAlloc_3943_, 1, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3943_, 2, v_attrs_3916_);
lean_ctor_set_uint8(v_reuseFailAlloc_3943_, sizeof(void*)*3, v_visibility_3911_);
lean_ctor_set_uint8(v_reuseFailAlloc_3943_, sizeof(void*)*3 + 1, v_isProtected_3912_);
lean_ctor_set_uint8(v_reuseFailAlloc_3943_, sizeof(void*)*3 + 2, v_computeKind_3913_);
lean_ctor_set_uint8(v_reuseFailAlloc_3943_, sizeof(void*)*3 + 3, v_recKind_3914_);
lean_ctor_set_uint8(v_reuseFailAlloc_3943_, sizeof(void*)*3 + 4, v_isUnsafe_3915_);
v___x_3928_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; uint8_t v___x_3930_; uint8_t v___y_3932_; 
v___x_3929_ = l_Lean_Elab_Modifiers_filterAttrs(v___x_3928_, v___f_3925_);
v___x_3930_ = 0;
if (v_isGreatest_3909_ == 0)
{
uint8_t v___x_3941_; 
v___x_3941_ = 2;
v___y_3932_ = v___x_3941_;
goto v___jp_3931_;
}
else
{
uint8_t v___x_3942_; 
v___x_3942_ = 1;
v___y_3932_ = v___x_3942_;
goto v___jp_3931_;
}
v___jp_3931_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; size_t v___x_3937_; size_t v___x_3938_; lean_object* v___x_3939_; 
lean_inc_n(v_ref_3908_, 4);
v___x_3933_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3933_, 0, v_ref_3908_);
lean_ctor_set(v___x_3933_, 1, v___x_3926_);
lean_ctor_set_uint8(v___x_3933_, sizeof(void*)*2, v___y_3932_);
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3933_);
v___x_3935_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3935_, 0, v_ref_3908_);
lean_ctor_set(v___x_3935_, 1, v___x_3926_);
lean_ctor_set(v___x_3935_, 2, v___x_3926_);
lean_ctor_set(v___x_3935_, 3, v___x_3934_);
lean_ctor_set(v___x_3935_, 4, v___x_3926_);
lean_ctor_set(v___x_3935_, 5, v___x_3903_);
lean_inc(v_snd_3923_);
lean_inc(v_fst_3922_);
lean_inc(v___x_3896_);
v___x_3936_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v___x_3936_, 0, v_ref_3908_);
lean_ctor_set(v___x_3936_, 1, v___x_3896_);
lean_ctor_set(v___x_3936_, 2, v___x_3929_);
lean_ctor_set(v___x_3936_, 3, v_fst_3922_);
lean_ctor_set(v___x_3936_, 4, v_ref_3908_);
lean_ctor_set(v___x_3936_, 5, v___x_3903_);
lean_ctor_set(v___x_3936_, 6, v_snd_3923_);
lean_ctor_set(v___x_3936_, 7, v_v_3902_);
lean_ctor_set(v___x_3936_, 8, v___x_3935_);
lean_ctor_set_uint8(v___x_3936_, sizeof(void*)*9, v___x_3930_);
v___x_3937_ = ((size_t)1ULL);
v___x_3938_ = lean_usize_add(v_i_3898_, v___x_3937_);
v___x_3939_ = lean_array_uset(v_bs_x27_3904_, v_i_3898_, v___x_3936_);
v_i_3898_ = v___x_3938_;
v_bs_3899_ = v___x_3939_;
goto _start;
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
lean_object* v_v_4006_; lean_object* v_declName_4007_; lean_object* v___x_4008_; 
v_v_4006_ = lean_array_uget_borrowed(v_bs_3996_, v_i_3995_);
v_declName_4007_ = lean_ctor_get(v_v_4006_, 1);
lean_inc(v_declName_4007_);
v___x_4008_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_Command_elabCoinductive_spec__0(v_declName_4007_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; lean_object* v_bs_x27_4011_; size_t v___x_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = lean_unsigned_to_nat(0u);
v_bs_x27_4011_ = lean_array_uset(v_bs_3996_, v_i_3995_, v___x_4010_);
v___x_4012_ = ((size_t)1ULL);
v___x_4013_ = lean_usize_add(v_i_3995_, v___x_4012_);
v___x_4014_ = lean_array_uset(v_bs_x27_4011_, v_i_3995_, v_a_4009_);
v_i_3995_ = v___x_4013_;
v_bs_3996_ = v___x_4014_;
goto _start;
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v_bs_3996_);
v_a_4016_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4008_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4008_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(lean_object* v_v_4069_, lean_object* v___x_4070_, lean_object* v___x_4071_, uint8_t v___x_4072_, lean_object* v_args_4073_, lean_object* v_body_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_numParams_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; 
v_numParams_4082_ = lean_ctor_get(v_v_4069_, 1);
lean_inc(v_numParams_4082_);
lean_dec(v_v_4069_);
lean_inc_ref(v_args_4073_);
v___x_4083_ = l_Array_toSubarray___redArg(v_args_4073_, v___x_4070_, v___x_4071_);
v___x_4084_ = l_Subarray_copy___redArg(v___x_4083_);
v___x_4085_ = lean_array_get_size(v_args_4073_);
v___x_4086_ = l_Array_toSubarray___redArg(v_args_4073_, v_numParams_4082_, v___x_4085_);
v___x_4087_ = l_Subarray_copy___redArg(v___x_4086_);
v___x_4088_ = l_Array_append___redArg(v___x_4084_, v___x_4087_);
lean_dec_ref(v___x_4087_);
v___x_4089_ = 0;
v___x_4090_ = 1;
v___x_4091_ = l_Lean_Meta_mkForallFVars(v___x_4088_, v_body_4074_, v___x_4089_, v___x_4072_, v___x_4072_, v___x_4090_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec_ref(v___x_4088_);
return v___x_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed(lean_object* v_v_4092_, lean_object* v___x_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, lean_object* v_args_4096_, lean_object* v_body_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
uint8_t v___x_6152__boxed_4105_; lean_object* v_res_4106_; 
v___x_6152__boxed_4105_ = lean_unbox(v___x_4095_);
v_res_4106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0(v_v_4092_, v___x_4093_, v___x_4094_, v___x_6152__boxed_4105_, v_args_4096_, v_body_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(lean_object* v___x_4107_, size_t v_sz_4108_, size_t v_i_4109_, lean_object* v_bs_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_){
_start:
{
uint8_t v___x_4118_; 
v___x_4118_ = lean_usize_dec_lt(v_i_4109_, v_sz_4108_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; 
lean_dec(v___x_4107_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v_bs_4110_);
return v___x_4119_;
}
else
{
lean_object* v_v_4120_; lean_object* v_toConstantVal_4121_; lean_object* v_name_4122_; lean_object* v_type_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___f_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; 
v_v_4120_ = lean_array_uget_borrowed(v_bs_4110_, v_i_4109_);
v_toConstantVal_4121_ = lean_ctor_get(v_v_4120_, 0);
v_name_4122_ = lean_ctor_get(v_toConstantVal_4121_, 0);
lean_inc(v_name_4122_);
v_type_4123_ = lean_ctor_get(v_toConstantVal_4121_, 2);
v___x_4124_ = lean_unsigned_to_nat(0u);
v___x_4125_ = lean_box(v___x_4118_);
lean_inc(v___x_4107_);
lean_inc(v_v_4120_);
v___f_4126_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2___lam__0___boxed), 13, 4);
lean_closure_set(v___f_4126_, 0, v_v_4120_);
lean_closure_set(v___f_4126_, 1, v___x_4124_);
lean_closure_set(v___f_4126_, 2, v___x_4107_);
lean_closure_set(v___f_4126_, 3, v___x_4125_);
v___x_4127_ = 0;
lean_inc_ref(v_type_4123_);
v___x_4128_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__6___redArg(v_type_4123_, v___f_4126_, v___x_4127_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v_bs_x27_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; size_t v___x_4133_; size_t v___x_4134_; lean_object* v___x_4135_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v_bs_x27_4130_ = lean_array_uset(v_bs_4110_, v_i_4109_, v___x_4124_);
v___x_4131_ = l_Lean_Elab_Command_removeFunctorPostfix(v_name_4122_);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
lean_ctor_set(v___x_4132_, 1, v_a_4129_);
v___x_4133_ = ((size_t)1ULL);
v___x_4134_ = lean_usize_add(v_i_4109_, v___x_4133_);
v___x_4135_ = lean_array_uset(v_bs_x27_4130_, v_i_4109_, v___x_4132_);
v_i_4109_ = v___x_4134_;
v_bs_4110_ = v___x_4135_;
goto _start;
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v_name_4122_);
lean_dec_ref(v_bs_4110_);
lean_dec(v___x_4107_);
v_a_4137_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4128_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4128_);
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
lean_object* v_options_4191_; lean_object* v_inheritedTraceOptions_4192_; uint8_t v_hasTrace_4193_; lean_object* v___x_4194_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; 
v_options_4191_ = lean_ctor_get(v_a_4188_, 2);
v_inheritedTraceOptions_4192_ = lean_ctor_get(v_a_4188_, 13);
v_hasTrace_4193_ = lean_ctor_get_uint8(v_options_4191_, sizeof(void*)*1);
v___x_4194_ = l_Lean_instInhabitedInductiveVal_default;
if (v_hasTrace_4193_ == 0)
{
v___y_4196_ = v_a_4184_;
v___y_4197_ = v_a_4185_;
v___y_4198_ = v_a_4186_;
v___y_4199_ = v_a_4187_;
v___y_4200_ = v_a_4188_;
v___y_4201_ = v_a_4189_;
goto v___jp_4195_;
}
else
{
lean_object* v_cls_4263_; lean_object* v___x_4264_; uint8_t v___x_4265_; 
v_cls_4263_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_initFn___closed__2_00___x40_Lean_Elab_Coinductive_793488904____hygCtx___hyg_2_));
v___x_4264_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__9___closed__4);
v___x_4265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4192_, v_options_4191_, v___x_4264_);
if (v___x_4265_ == 0)
{
v___y_4196_ = v_a_4184_;
v___y_4197_ = v_a_4185_;
v___y_4198_ = v_a_4186_;
v___y_4199_ = v_a_4187_;
v___y_4200_ = v_a_4188_;
v___y_4201_ = v_a_4189_;
goto v___jp_4195_;
}
else
{
lean_object* v___x_4266_; size_t v_sz_4267_; size_t v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4266_ = lean_obj_once(&l_Lean_Elab_Command_elabCoinductive___closed__1, &l_Lean_Elab_Command_elabCoinductive___closed__1_once, _init_l_Lean_Elab_Command_elabCoinductive___closed__1);
v_sz_4267_ = lean_array_size(v_coinductiveElabData_4183_);
v___x_4268_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4183_);
v___x_4269_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__6(v_sz_4267_, v___x_4268_, v_coinductiveElabData_4183_);
v___x_4270_ = lean_array_to_list(v___x_4269_);
v___x_4271_ = lean_box(0);
v___x_4272_ = l_List_mapTR_loop___at___00Lean_Elab_Command_elabCoinductive_spec__7(v___x_4270_, v___x_4271_);
v___x_4273_ = l_Lean_MessageData_ofList(v___x_4272_);
v___x_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4266_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = l_Lean_addTrace___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__5___redArg(v_cls_4263_, v___x_4274_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_dec_ref_known(v___x_4275_, 1);
v___y_4196_ = v_a_4184_;
v___y_4197_ = v_a_4185_;
v___y_4198_ = v_a_4186_;
v___y_4199_ = v_a_4187_;
v___y_4200_ = v_a_4188_;
v___y_4201_ = v_a_4189_;
goto v___jp_4195_;
}
else
{
lean_dec_ref(v_coinductiveElabData_4183_);
return v___x_4275_;
}
}
}
v___jp_4195_:
{
size_t v_sz_4202_; size_t v___x_4203_; lean_object* v___x_4204_; 
v_sz_4202_ = lean_array_size(v_coinductiveElabData_4183_);
v___x_4203_ = ((size_t)0ULL);
lean_inc_ref(v_coinductiveElabData_4183_);
v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__1(v_sz_4202_, v___x_4203_, v_coinductiveElabData_4183_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v_toConstantVal_4208_; lean_object* v_numParams_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; size_t v_sz_4212_; lean_object* v___x_4213_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc_n(v_a_4205_, 2);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = lean_unsigned_to_nat(0u);
v___x_4207_ = lean_array_get_borrowed(v___x_4194_, v_a_4205_, v___x_4206_);
v_toConstantVal_4208_ = lean_ctor_get(v___x_4207_, 0);
v_numParams_4209_ = lean_ctor_get(v___x_4207_, 1);
v___x_4210_ = lean_array_get_size(v_a_4205_);
v___x_4211_ = lean_nat_sub(v_numParams_4209_, v___x_4210_);
v_sz_4212_ = lean_array_size(v_a_4205_);
lean_inc(v___x_4211_);
v___x_4213_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__2(v___x_4211_, v_sz_4212_, v___x_4203_, v_a_4205_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v_levelParams_4215_; lean_object* v_type_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; size_t v_sz_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___f_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; lean_object* v___x_4226_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc_n(v_a_4214_, 2);
lean_dec_ref_known(v___x_4213_, 1);
v_levelParams_4215_ = lean_ctor_get(v_toConstantVal_4208_, 1);
v_type_4216_ = lean_ctor_get(v_toConstantVal_4208_, 2);
v___x_4217_ = lean_box(0);
lean_inc(v_levelParams_4215_);
v___x_4218_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas_spec__0(v_levelParams_4215_, v___x_4217_);
v_sz_4219_ = lean_array_size(v_a_4214_);
lean_inc(v___x_4218_);
v___x_4220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__3(v___x_4218_, v_sz_4219_, v___x_4203_, v_a_4214_);
v___x_4221_ = lean_box_usize(v_sz_4212_);
v___x_4222_ = ((lean_object*)(l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor___boxed__const__1));
lean_inc(v_a_4205_);
v___f_4223_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabCoinductive___lam__0___boxed), 14, 5);
lean_closure_set(v___f_4223_, 0, v___x_4218_);
lean_closure_set(v___f_4223_, 1, v___x_4220_);
lean_closure_set(v___f_4223_, 2, v___x_4221_);
lean_closure_set(v___f_4223_, 3, v___x_4222_);
lean_closure_set(v___f_4223_, 4, v_a_4205_);
lean_inc(v___x_4211_);
v___x_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4211_);
v___x_4225_ = 0;
lean_inc_ref(v_type_4216_);
v___x_4226_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructor_spec__8___redArg(v_type_4216_, v___x_4224_, v___f_4223_, v___x_4225_, v___x_4225_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v_a_4227_; lean_object* v___x_4228_; lean_object* v_env_4229_; size_t v_sz_4230_; lean_object* v_lctx_4231_; lean_object* v_localInstances_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref_known(v___x_4226_, 1);
v___x_4228_ = lean_st_ref_get(v___y_4201_);
v_env_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc_ref(v_env_4229_);
lean_dec(v___x_4228_);
v_sz_4230_ = lean_array_size(v_a_4227_);
v_lctx_4231_ = lean_ctor_get(v___y_4198_, 2);
v_localInstances_4232_ = lean_ctor_get(v___y_4198_, 3);
lean_inc(v_levelParams_4215_);
v___x_4233_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4183_, v_env_4229_, v_a_4214_, v_levelParams_4215_, v_sz_4230_, v___x_4203_, v_a_4227_);
lean_dec(v_a_4214_);
lean_inc_ref(v_localInstances_4232_);
lean_inc_ref(v_lctx_4231_);
v___x_4234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4234_, 0, v_lctx_4231_);
lean_ctor_set(v___x_4234_, 1, v_localInstances_4232_);
v___x_4235_ = l_Lean_Elab_partialFixpoint(v___x_4234_, v___x_4233_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v___x_4236_; 
lean_dec_ref_known(v___x_4235_, 1);
lean_inc(v_a_4205_);
v___x_4236_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateEqLemmas(v_a_4205_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v___x_4237_; 
lean_dec_ref_known(v___x_4236_, 1);
lean_inc(v_a_4205_);
v___x_4237_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_generateCoinductiveConstructors(v___x_4211_, v_a_4205_, v_coinductiveElabData_4183_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v___x_4238_; 
lean_dec_ref_known(v___x_4237_, 1);
v___x_4238_ = l___private_Lean_Elab_Coinductive_0__Lean_Elab_Command_mkCasesOnCoinductive(v_a_4205_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
return v___x_4238_;
}
else
{
lean_dec(v_a_4205_);
return v___x_4237_;
}
}
else
{
lean_dec(v___x_4211_);
lean_dec(v_a_4205_);
lean_dec_ref(v_coinductiveElabData_4183_);
return v___x_4236_;
}
}
else
{
lean_dec(v___x_4211_);
lean_dec(v_a_4205_);
lean_dec_ref(v_coinductiveElabData_4183_);
return v___x_4235_;
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v_a_4214_);
lean_dec(v___x_4211_);
lean_dec(v_a_4205_);
lean_dec_ref(v_coinductiveElabData_4183_);
v_a_4239_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4226_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4226_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
else
{
lean_object* v_a_4247_; lean_object* v___x_4249_; uint8_t v_isShared_4250_; uint8_t v_isSharedCheck_4254_; 
lean_dec(v___x_4211_);
lean_dec(v_a_4205_);
lean_dec_ref(v_coinductiveElabData_4183_);
v_a_4247_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4254_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4254_ == 0)
{
v___x_4249_ = v___x_4213_;
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
else
{
lean_inc(v_a_4247_);
lean_dec(v___x_4213_);
v___x_4249_ = lean_box(0);
v_isShared_4250_ = v_isSharedCheck_4254_;
goto v_resetjp_4248_;
}
v_resetjp_4248_:
{
lean_object* v___x_4252_; 
if (v_isShared_4250_ == 0)
{
v___x_4252_ = v___x_4249_;
goto v_reusejp_4251_;
}
else
{
lean_object* v_reuseFailAlloc_4253_; 
v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_a_4247_);
v___x_4252_ = v_reuseFailAlloc_4253_;
goto v_reusejp_4251_;
}
v_reusejp_4251_:
{
return v___x_4252_;
}
}
}
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
lean_dec_ref(v_coinductiveElabData_4183_);
v_a_4255_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4257_ = v___x_4204_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4204_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Command_elabCoinductive___boxed(lean_object* v_coinductiveElabData_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lean_Elab_Command_elabCoinductive(v_coinductiveElabData_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(lean_object* v___x_4285_, lean_object* v___x_4286_, lean_object* v_params_4287_, size_t v_sz_4288_, size_t v_i_4289_, lean_object* v_bs_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
lean_object* v___x_4298_; 
v___x_4298_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___redArg(v___x_4285_, v___x_4286_, v_params_4287_, v_sz_4288_, v_i_4289_, v_bs_4290_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4___boxed(lean_object* v___x_4299_, lean_object* v___x_4300_, lean_object* v_params_4301_, lean_object* v_sz_4302_, lean_object* v_i_4303_, lean_object* v_bs_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
size_t v_sz_boxed_4312_; size_t v_i_boxed_4313_; lean_object* v_res_4314_; 
v_sz_boxed_4312_ = lean_unbox_usize(v_sz_4302_);
lean_dec(v_sz_4302_);
v_i_boxed_4313_ = lean_unbox_usize(v_i_4303_);
lean_dec(v_i_4303_);
v_res_4314_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__4(v___x_4299_, v___x_4300_, v_params_4301_, v_sz_boxed_4312_, v_i_boxed_4313_, v_bs_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(lean_object* v_coinductiveElabData_4315_, lean_object* v___x_4316_, lean_object* v_a_4317_, lean_object* v___x_4318_, lean_object* v_as_4319_, size_t v_sz_4320_, size_t v_i_4321_, lean_object* v_bs_4322_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___redArg(v_coinductiveElabData_4315_, v___x_4316_, v_a_4317_, v___x_4318_, v_sz_4320_, v_i_4321_, v_bs_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5___boxed(lean_object* v_coinductiveElabData_4324_, lean_object* v___x_4325_, lean_object* v_a_4326_, lean_object* v___x_4327_, lean_object* v_as_4328_, lean_object* v_sz_4329_, lean_object* v_i_4330_, lean_object* v_bs_4331_){
_start:
{
size_t v_sz_boxed_4332_; size_t v_i_boxed_4333_; lean_object* v_res_4334_; 
v_sz_boxed_4332_ = lean_unbox_usize(v_sz_4329_);
lean_dec(v_sz_4329_);
v_i_boxed_4333_ = lean_unbox_usize(v_i_4330_);
lean_dec(v_i_4330_);
v_res_4334_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Command_elabCoinductive_spec__5(v_coinductiveElabData_4324_, v___x_4325_, v_a_4326_, v___x_4327_, v_as_4328_, v_sz_boxed_4332_, v_i_boxed_4333_, v_bs_4331_);
lean_dec_ref(v_as_4328_);
lean_dec_ref(v_a_4326_);
lean_dec_ref(v_coinductiveElabData_4324_);
return v_res_4334_;
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
