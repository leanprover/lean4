// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Preprocess
// Imports: public import Lean.Elab.Tactic.Simp
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
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_setNondep(lean_object*, uint8_t);
lean_object* l_Lean_LocalContext_addDecl(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isNondep(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_Simp_Result_addLambdas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "preprocess"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(215, 131, 155, 94, 122, 149, 97, 118)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 185, 233, 182, 178, 136, 28, 192)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "pre-process definitions defined by well-founded recursion with the `wf_preprocess` simp set"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(190, 109, 44, 197, 133, 51, 78, 82)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 26, 247, 251, 85, 18, 167, 105)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_wf_preprocess;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "wf_preprocess"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 210, 123, 148, 208, 214, 165, 77)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 164, .m_capacity = 164, .m_length = 163, .m_data = "simp lemma used in the preprocessing of well-founded recursive function definitions, in particular to add additional hypotheses to the context. Also see `wfParam`."};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "wfPreprocessSimpExtension"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 145, 22, 80, 3, 32, 9, 26)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_wfPreprocessSimpExtension;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_WF_isWfParam_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wfParam"};
static const lean_object* l_Lean_Elab_WF_isWfParam_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_WF_isWfParam_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Elab_WF_isWfParam_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_isWfParam_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 61, 210, 169, 58, 176, 246, 156)}};
static const lean_object* l_Lean_Elab_WF_isWfParam_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_WF_isWfParam_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_WF_paramProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_WF_paramProj___closed__0 = (const lean_object*)&l_Lean_Elab_WF_paramProj___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "paramProj"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(185, 166, 16, 253, 90, 4, 64, 220)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "paramMatcher"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(136, 249, 169, 242, 162, 242, 251, 234)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "assertion violation: num > 0\n      "};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "_private.Lean.Elab.PreDefinition.WF.Preprocess.0.Lean.Elab.WF.processParamLet"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Elab.PreDefinition.WF.Preprocess"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "paramLet"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(158, 69, 53, 139, 5, 90, 17, 138)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12____boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0;
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__0;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__1;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__2;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__3;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__4;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__5;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__6;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__7;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__8;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__9;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__10_value;
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__11_value;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__12 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__12_value;
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__13_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__14;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Attach-introduction:"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__15 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__15_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__16;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\nto"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__17 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__17_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__18;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\ncleand up to "};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__19 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__19_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__20;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_WF_preprocess___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_WF_preprocess___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_WF_preprocess___closed__0 = (const lean_object*)&l_Lean_Elab_WF_preprocess___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_54_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4____boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_71_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_72_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_73_ = l_Lean_Meta_registerSimpAttr(v___x_70_, v___x_71_, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2____boxed(lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
return v_res_75_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_box(0);
v___x_77_ = lean_unsigned_to_nat(16u);
v___x_78_ = lean_mk_array(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2(void){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_82_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; 
v___x_85_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3);
v___x_86_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1);
v___x_87_ = 1;
v___x_88_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_85_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*2, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = l_Lean_Elab_WF_wfPreprocessSimpExtension;
v___x_94_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_93_, v_a_91_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_96_; lean_object* v_maxSteps_97_; lean_object* v_maxDischargeDepth_98_; uint8_t v_contextual_99_; uint8_t v_memoize_100_; uint8_t v_singlePass_101_; uint8_t v_zeta_102_; uint8_t v_beta_103_; uint8_t v_eta_104_; uint8_t v_etaStruct_105_; uint8_t v_iota_106_; uint8_t v_proj_107_; uint8_t v_decide_108_; uint8_t v_arith_109_; uint8_t v_autoUnfold_110_; uint8_t v_failIfUnchanged_111_; uint8_t v_ground_112_; uint8_t v_unfoldPartialApp_113_; uint8_t v_zetaDelta_114_; uint8_t v_index_115_; uint8_t v_implicitDefEqProofs_116_; uint8_t v_zetaUnused_117_; uint8_t v_catchRuntime_118_; uint8_t v_zetaHave_119_; uint8_t v_letToHave_120_; uint8_t v_bitVecOfNat_121_; uint8_t v_warnExponents_122_; uint8_t v_suggestions_123_; lean_object* v_maxSuggestions_124_; uint8_t v_locals_125_; uint8_t v_instances_126_; uint8_t v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
lean_dec_ref_known(v___x_94_, 1);
v___x_96_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_97_ = lean_ctor_get(v___x_96_, 0);
v_maxDischargeDepth_98_ = lean_ctor_get(v___x_96_, 1);
v_contextual_99_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3);
v_memoize_100_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 1);
v_singlePass_101_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 2);
v_zeta_102_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 3);
v_beta_103_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 4);
v_eta_104_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 5);
v_etaStruct_105_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 6);
v_iota_106_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 7);
v_proj_107_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 8);
v_decide_108_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 9);
v_arith_109_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 10);
v_autoUnfold_110_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 11);
v_failIfUnchanged_111_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 13);
v_ground_112_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_113_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 15);
v_zetaDelta_114_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 16);
v_index_115_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_116_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 18);
v_zetaUnused_117_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 19);
v_catchRuntime_118_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 20);
v_zetaHave_119_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 21);
v_letToHave_120_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 22);
v_bitVecOfNat_121_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 24);
v_warnExponents_122_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 25);
v_suggestions_123_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 26);
v_maxSuggestions_124_ = lean_ctor_get(v___x_96_, 2);
v_locals_125_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 27);
v_instances_126_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*3 + 28);
v___x_127_ = 1;
v___x_128_ = 0;
lean_inc(v_maxSuggestions_124_);
lean_inc(v_maxDischargeDepth_98_);
lean_inc(v_maxSteps_97_);
v___x_129_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_129_, 0, v_maxSteps_97_);
lean_ctor_set(v___x_129_, 1, v_maxDischargeDepth_98_);
lean_ctor_set(v___x_129_, 2, v_maxSuggestions_124_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3, v_contextual_99_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 1, v_memoize_100_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 2, v_singlePass_101_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 3, v_zeta_102_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 4, v_beta_103_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 5, v_eta_104_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 6, v_etaStruct_105_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 7, v_iota_106_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 8, v_proj_107_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 9, v_decide_108_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 10, v_arith_109_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 11, v_autoUnfold_110_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 12, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 13, v_failIfUnchanged_111_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 14, v_ground_112_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 15, v_unfoldPartialApp_113_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 16, v_zetaDelta_114_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 17, v_index_115_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_116_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 19, v_zetaUnused_117_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 20, v_catchRuntime_118_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 21, v_zetaHave_119_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 22, v_letToHave_120_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 23, v___x_128_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 24, v_bitVecOfNat_121_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 25, v_warnExponents_122_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 26, v_suggestions_123_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 27, v_locals_125_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*3 + 28, v_instances_126_);
v___x_130_ = lean_unsigned_to_nat(1u);
v___x_131_ = lean_mk_empty_array_with_capacity(v___x_130_);
v___x_132_ = lean_array_push(v___x_131_, v_a_95_);
v___x_133_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4);
v___x_134_ = l_Lean_Options_empty;
v___x_135_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_129_, v___x_132_, v___x_133_, v___x_134_, v_a_89_, v_a_90_, v_a_91_);
return v___x_135_;
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
v_a_136_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_94_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_94_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___boxed(lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec_ref(v_a_144_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_149_, v_a_151_, v_a_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___boxed(lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(v_a_155_, v_a_156_, v_a_157_, v_a_158_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f(lean_object* v_e_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_165_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_166_ = lean_unsigned_to_nat(2u);
v___x_167_ = l_Lean_Expr_isAppOfArity(v_e_164_, v___x_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_box(0);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = l_Lean_Expr_appArg_x21(v_e_164_);
v___x_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f___boxed(lean_object* v_e_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Elab_WF_isWfParam_x3f(v_e_171_);
lean_dec_ref(v_e_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam(lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_180_ = lean_unsigned_to_nat(1u);
v___x_181_ = lean_mk_empty_array_with_capacity(v___x_180_);
v___x_182_ = lean_array_push(v___x_181_, v_e_173_);
v___x_183_ = l_Lean_Meta_mkAppM(v___x_179_, v___x_182_, v_a_174_, v_a_175_, v_a_176_, v_a_177_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam___boxed(lean_object* v_e_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Elab_WF_mkWfParam(v_e_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(lean_object* v_declName_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; lean_object* v_env_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = lean_st_ref_get(v___y_192_);
v_env_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc_ref(v_env_195_);
lean_dec(v___x_194_);
v___x_196_ = l_Lean_Environment_isProjectionFn(v_env_195_, v_declName_191_);
v___x_197_ = lean_box(v___x_196_);
v___x_198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg___boxed(lean_object* v_declName_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_199_, v___y_200_);
lean_dec(v___y_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(lean_object* v_declName_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_203_, v___y_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___boxed(lean_object* v_declName_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(v_declName_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj(lean_object* v_e_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
uint8_t v___x_234_; 
v___x_234_ = l_Lean_Expr_isApp(v_e_225_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec_ref(v_e_225_);
v___x_235_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
else
{
lean_object* v_fn_237_; lean_object* v_arg_238_; lean_object* v___x_239_; 
v_fn_237_ = lean_ctor_get(v_e_225_, 0);
lean_inc_ref(v_fn_237_);
v_arg_238_ = lean_ctor_get(v_e_225_, 1);
v___x_239_ = l_Lean_Elab_WF_isWfParam_x3f(v_arg_238_);
if (lean_obj_tag(v___x_239_) == 1)
{
lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_283_; 
v_val_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_283_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_283_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_283_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v_f_244_; uint8_t v___x_245_; 
v_f_244_ = l_Lean_Expr_getAppFn(v_e_225_);
lean_dec_ref(v_e_225_);
v___x_245_ = l_Lean_Expr_isConst(v_f_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_dec_ref(v_f_244_);
lean_dec(v_val_240_);
lean_dec_ref(v_fn_237_);
v___x_246_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v___x_246_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_282_; 
v___x_250_ = l_Lean_Expr_constName_x21(v_f_244_);
lean_dec_ref(v_f_244_);
v___x_251_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v___x_250_, v_a_232_);
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_282_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_282_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_282_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; 
v___x_256_ = lean_unbox(v_a_252_);
lean_dec(v_a_252_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_259_; 
lean_del_object(v___x_242_);
lean_dec(v_val_240_);
lean_dec_ref(v_fn_237_);
v___x_257_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_del_object(v___x_254_);
v___x_261_ = l_Lean_Expr_app___override(v_fn_237_, v_val_240_);
v___x_262_ = l_Lean_Elab_WF_mkWfParam(v___x_261_, v_a_229_, v_a_230_, v_a_231_, v_a_232_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_273_ == 0)
{
v___x_265_ = v___x_262_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 0);
lean_ctor_set(v___x_242_, 0, v_a_263_);
v___x_268_ = v___x_242_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_268_);
v___x_270_ = v___x_265_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_del_object(v___x_242_);
v_a_274_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_262_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_262_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
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
lean_object* v___x_284_; lean_object* v___x_285_; 
lean_dec(v___x_239_);
lean_dec_ref(v_fn_237_);
lean_dec_ref(v_e_225_);
v___x_284_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___boxed(lean_object* v_e_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Elab_WF_paramProj(v_e_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_308_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_309_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_310_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_307_, v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12____boxed(lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_();
return v_res_312_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_317_ = 1;
v___x_318_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14__once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_);
v___x_319_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_316_, v___x_317_, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14____boxed(lean_object* v_a_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_();
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(lean_object* v_k_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v_b_326_, lean_object* v_c_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; 
lean_inc(v___y_331_);
lean_inc_ref(v___y_330_);
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_325_);
lean_inc_ref(v___y_324_);
lean_inc(v___y_323_);
v___x_333_ = lean_apply_10(v_k_322_, v_b_326_, v_c_327_, v___y_323_, v___y_324_, v___y_325_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, lean_box(0));
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object* v_k_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v_b_338_, lean_object* v_c_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(v_k_334_, v___y_335_, v___y_336_, v___y_337_, v_b_338_, v_c_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object* v_e_346_, lean_object* v_k_347_, uint8_t v_cleanupAnnotations_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___f_357_; uint8_t v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_inc(v___y_351_);
lean_inc_ref(v___y_350_);
lean_inc(v___y_349_);
v___f_357_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_357_, 0, v_k_347_);
lean_closure_set(v___f_357_, 1, v___y_349_);
lean_closure_set(v___f_357_, 2, v___y_350_);
lean_closure_set(v___f_357_, 3, v___y_351_);
v___x_358_ = 1;
v___x_359_ = 0;
v___x_360_ = lean_box(0);
v___x_361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_346_, v___x_358_, v___x_359_, v___x_358_, v___x_359_, v___x_360_, v___f_357_, v_cleanupAnnotations_348_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_361_) == 0)
{
return v___x_361_;
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___boxed(lean_object* v_e_370_, lean_object* v_k_371_, lean_object* v_cleanupAnnotations_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_381_; lean_object* v_res_382_; 
v_cleanupAnnotations_boxed_381_ = lean_unbox(v_cleanupAnnotations_372_);
v_res_382_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_370_, v_k_371_, v_cleanupAnnotations_boxed_381_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_object* v_00_u03b1_383_, lean_object* v_e_384_, lean_object* v_k_385_, uint8_t v_cleanupAnnotations_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_384_, v_k_385_, v_cleanupAnnotations_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___boxed(lean_object* v_00_u03b1_396_, lean_object* v_e_397_, lean_object* v_k_398_, lean_object* v_cleanupAnnotations_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_408_; lean_object* v_res_409_; 
v_cleanupAnnotations_boxed_408_ = lean_unbox(v_cleanupAnnotations_399_);
v_res_409_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(v_00_u03b1_396_, v_e_397_, v_k_398_, v_cleanupAnnotations_boxed_408_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t v_sz_410_, size_t v_i_411_, lean_object* v_bs_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_lt(v_i_411_, v_sz_410_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_419_, 0, v_bs_412_);
return v___x_419_;
}
else
{
lean_object* v_v_420_; lean_object* v___x_421_; 
v_v_420_ = lean_array_uget_borrowed(v_bs_412_, v_i_411_);
lean_inc(v_v_420_);
v___x_421_ = l_Lean_Elab_WF_mkWfParam(v_v_420_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_a_422_; lean_object* v___x_423_; lean_object* v_bs_x27_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v___x_427_; 
v_a_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_a_422_);
lean_dec_ref_known(v___x_421_, 1);
v___x_423_ = lean_unsigned_to_nat(0u);
v_bs_x27_424_ = lean_array_uset(v_bs_412_, v_i_411_, v___x_423_);
v___x_425_ = ((size_t)1ULL);
v___x_426_ = lean_usize_add(v_i_411_, v___x_425_);
v___x_427_ = lean_array_uset(v_bs_x27_424_, v_i_411_, v_a_422_);
v_i_411_ = v___x_426_;
v_bs_412_ = v___x_427_;
goto _start;
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec_ref(v_bs_412_);
v_a_429_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_421_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_421_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object* v_sz_437_, lean_object* v_i_438_, lean_object* v_bs_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
size_t v_sz_boxed_445_; size_t v_i_boxed_446_; lean_object* v_res_447_; 
v_sz_boxed_445_ = lean_unbox_usize(v_sz_437_);
lean_dec(v_sz_437_);
v_i_boxed_446_ = lean_unbox_usize(v_i_438_);
lean_dec(v_i_438_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_boxed_445_, v_i_boxed_446_, v_bs_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(uint8_t v___x_448_, lean_object* v_xs_449_, lean_object* v_body_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
size_t v_sz_459_; size_t v___x_460_; lean_object* v___x_461_; 
v_sz_459_ = lean_array_size(v_xs_449_);
v___x_460_ = ((size_t)0ULL);
lean_inc_ref(v_xs_449_);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_459_, v___x_460_, v_xs_449_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; uint8_t v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
v___x_463_ = l_Lean_Expr_replaceFVars(v_body_450_, v_xs_449_, v_a_462_);
lean_dec(v_a_462_);
v___x_464_ = 0;
v___x_465_ = 1;
v___x_466_ = l_Lean_Meta_mkLambdaFVars(v_xs_449_, v___x_463_, v___x_464_, v___x_448_, v___x_464_, v___x_448_, v___x_465_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec_ref(v_xs_449_);
return v___x_466_;
}
else
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec_ref(v_xs_449_);
v_a_467_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_461_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_461_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0___boxed(lean_object* v___x_475_, lean_object* v_xs_476_, lean_object* v_body_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
uint8_t v___x_21870__boxed_486_; lean_object* v_res_487_; 
v___x_21870__boxed_486_ = lean_unbox(v___x_475_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(v___x_21870__boxed_486_, v_xs_476_, v_body_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v_body_477_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(size_t v_sz_488_, size_t v_i_489_, lean_object* v_bs_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_489_, v_sz_488_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v_bs_490_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; lean_object* v___f_502_; lean_object* v_v_503_; uint8_t v___x_504_; lean_object* v___x_505_; 
v___x_501_ = lean_box(v___x_499_);
v___f_502_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0___boxed), 11, 1);
lean_closure_set(v___f_502_, 0, v___x_501_);
v_v_503_ = lean_array_uget_borrowed(v_bs_490_, v_i_489_);
v___x_504_ = 0;
lean_inc(v_v_503_);
v___x_505_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_v_503_, v___f_502_, v___x_504_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v_bs_x27_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_a_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_unsigned_to_nat(0u);
v_bs_x27_508_ = lean_array_uset(v_bs_490_, v_i_489_, v___x_507_);
v___x_509_ = ((size_t)1ULL);
v___x_510_ = lean_usize_add(v_i_489_, v___x_509_);
v___x_511_ = lean_array_uset(v_bs_x27_508_, v_i_489_, v_a_506_);
v_i_489_ = v___x_510_;
v_bs_490_ = v___x_511_;
goto _start;
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v_bs_490_);
v_a_513_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_505_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_505_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___boxed(lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_bs_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
size_t v_sz_boxed_532_; size_t v_i_boxed_533_; lean_object* v_res_534_; 
v_sz_boxed_532_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_533_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_boxed_532_, v_i_boxed_533_, v_bs_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(lean_object* v_msgData_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v___x_541_; lean_object* v_env_542_; lean_object* v___x_543_; lean_object* v_mctx_544_; lean_object* v_lctx_545_; lean_object* v_options_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_541_ = lean_st_ref_get(v___y_539_);
v_env_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_env_542_);
lean_dec(v___x_541_);
v___x_543_ = lean_st_ref_get(v___y_537_);
v_mctx_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc_ref(v_mctx_544_);
lean_dec(v___x_543_);
v_lctx_545_ = lean_ctor_get(v___y_536_, 2);
v_options_546_ = lean_ctor_get(v___y_538_, 2);
lean_inc_ref(v_options_546_);
lean_inc_ref(v_lctx_545_);
v___x_547_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_547_, 0, v_env_542_);
lean_ctor_set(v___x_547_, 1, v_mctx_544_);
lean_ctor_set(v___x_547_, 2, v_lctx_545_);
lean_ctor_set(v___x_547_, 3, v_options_546_);
v___x_548_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_msgData_535_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16___boxed(lean_object* v_msgData_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msgData_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(lean_object* v_msg_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
v_ref_563_ = lean_ctor_get(v___y_560_, 5);
v___x_564_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_inc(v_ref_563_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v_ref_563_);
lean_ctor_set(v___x_569_, 1, v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 1);
lean_ctor_set(v___x_567_, 0, v___x_569_);
v___x_571_ = v___x_567_;
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
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg___boxed(lean_object* v_msg_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(lean_object* v_ref_581_, lean_object* v_msg_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_fileName_591_; lean_object* v_fileMap_592_; lean_object* v_options_593_; lean_object* v_currRecDepth_594_; lean_object* v_maxRecDepth_595_; lean_object* v_ref_596_; lean_object* v_currNamespace_597_; lean_object* v_openDecls_598_; lean_object* v_initHeartbeats_599_; lean_object* v_maxHeartbeats_600_; lean_object* v_quotContext_601_; lean_object* v_currMacroScope_602_; uint8_t v_diag_603_; lean_object* v_cancelTk_x3f_604_; uint8_t v_suppressElabErrors_605_; lean_object* v_inheritedTraceOptions_606_; lean_object* v_ref_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v_fileName_591_ = lean_ctor_get(v___y_588_, 0);
v_fileMap_592_ = lean_ctor_get(v___y_588_, 1);
v_options_593_ = lean_ctor_get(v___y_588_, 2);
v_currRecDepth_594_ = lean_ctor_get(v___y_588_, 3);
v_maxRecDepth_595_ = lean_ctor_get(v___y_588_, 4);
v_ref_596_ = lean_ctor_get(v___y_588_, 5);
v_currNamespace_597_ = lean_ctor_get(v___y_588_, 6);
v_openDecls_598_ = lean_ctor_get(v___y_588_, 7);
v_initHeartbeats_599_ = lean_ctor_get(v___y_588_, 8);
v_maxHeartbeats_600_ = lean_ctor_get(v___y_588_, 9);
v_quotContext_601_ = lean_ctor_get(v___y_588_, 10);
v_currMacroScope_602_ = lean_ctor_get(v___y_588_, 11);
v_diag_603_ = lean_ctor_get_uint8(v___y_588_, sizeof(void*)*14);
v_cancelTk_x3f_604_ = lean_ctor_get(v___y_588_, 12);
v_suppressElabErrors_605_ = lean_ctor_get_uint8(v___y_588_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_606_ = lean_ctor_get(v___y_588_, 13);
v_ref_607_ = l_Lean_replaceRef(v_ref_581_, v_ref_596_);
lean_inc_ref(v_inheritedTraceOptions_606_);
lean_inc(v_cancelTk_x3f_604_);
lean_inc(v_currMacroScope_602_);
lean_inc(v_quotContext_601_);
lean_inc(v_maxHeartbeats_600_);
lean_inc(v_initHeartbeats_599_);
lean_inc(v_openDecls_598_);
lean_inc(v_currNamespace_597_);
lean_inc(v_maxRecDepth_595_);
lean_inc(v_currRecDepth_594_);
lean_inc_ref(v_options_593_);
lean_inc_ref(v_fileMap_592_);
lean_inc_ref(v_fileName_591_);
v___x_608_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_608_, 0, v_fileName_591_);
lean_ctor_set(v___x_608_, 1, v_fileMap_592_);
lean_ctor_set(v___x_608_, 2, v_options_593_);
lean_ctor_set(v___x_608_, 3, v_currRecDepth_594_);
lean_ctor_set(v___x_608_, 4, v_maxRecDepth_595_);
lean_ctor_set(v___x_608_, 5, v_ref_607_);
lean_ctor_set(v___x_608_, 6, v_currNamespace_597_);
lean_ctor_set(v___x_608_, 7, v_openDecls_598_);
lean_ctor_set(v___x_608_, 8, v_initHeartbeats_599_);
lean_ctor_set(v___x_608_, 9, v_maxHeartbeats_600_);
lean_ctor_set(v___x_608_, 10, v_quotContext_601_);
lean_ctor_set(v___x_608_, 11, v_currMacroScope_602_);
lean_ctor_set(v___x_608_, 12, v_cancelTk_x3f_604_);
lean_ctor_set(v___x_608_, 13, v_inheritedTraceOptions_606_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*14, v_diag_603_);
lean_ctor_set_uint8(v___x_608_, sizeof(void*)*14 + 1, v_suppressElabErrors_605_);
v___x_609_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_582_, v___y_586_, v___y_587_, v___x_608_, v___y_589_);
lean_dec_ref_known(v___x_608_, 14);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_610_, lean_object* v_msg_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_610_, v_msg_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec(v_ref_610_);
return v_res_620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
lean_ctor_set(v___x_626_, 3, v___x_625_);
lean_ctor_set(v___x_626_, 4, v___x_624_);
lean_ctor_set(v___x_626_, 5, v___x_624_);
lean_ctor_set(v___x_626_, 6, v___x_624_);
lean_ctor_set(v___x_626_, 7, v___x_624_);
lean_ctor_set(v___x_626_, 8, v___x_624_);
lean_ctor_set(v___x_626_, 9, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_unsigned_to_nat(32u);
v___x_628_ = lean_mk_empty_array_with_capacity(v___x_627_);
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = ((size_t)5ULL);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_unsigned_to_nat(32u);
v___x_633_ = lean_mk_empty_array_with_capacity(v___x_632_);
v___x_634_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_635_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_631_);
lean_ctor_set(v___x_635_, 3, v___x_631_);
lean_ctor_set_usize(v___x_635_, 4, v___x_630_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_box(1);
v___x_637_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_637_);
lean_ctor_set(v___x_639_, 2, v___x_636_);
return v___x_639_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_660_ = l_Lean_stringToMessageData(v___x_659_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_661_, lean_object* v_declHint_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; lean_object* v_env_666_; uint8_t v___y_668_; uint8_t v___x_724_; uint8_t v___x_725_; 
v___x_665_ = lean_st_ref_get(v___y_663_);
v_env_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc_ref(v_env_666_);
lean_dec(v___x_665_);
v___x_724_ = l_Lean_Name_isAnonymous(v_declHint_662_);
v___x_725_ = lean_bool_not(v___x_724_);
if (v___x_725_ == 0)
{
v___y_668_ = v___x_725_;
goto v___jp_667_;
}
else
{
uint8_t v_isExporting_726_; 
v_isExporting_726_ = lean_ctor_get_uint8(v_env_666_, sizeof(void*)*8);
v___y_668_ = v_isExporting_726_;
goto v___jp_667_;
}
v___jp_667_:
{
if (v___y_668_ == 0)
{
lean_object* v___x_669_; 
lean_dec_ref(v_env_666_);
lean_dec(v_declHint_662_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_msg_661_);
return v___x_669_;
}
else
{
uint8_t v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_670_ = 0;
lean_inc_ref(v_env_666_);
v___x_671_ = l_Lean_Environment_setExporting(v_env_666_, v___x_670_);
lean_inc(v_declHint_662_);
lean_inc_ref(v___x_671_);
v___x_672_ = l_Lean_Environment_contains(v___x_671_, v_declHint_662_, v___y_668_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v___x_671_);
lean_dec_ref(v_env_666_);
lean_dec(v_declHint_662_);
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v_msg_661_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_c_679_; lean_object* v___x_680_; 
v___x_674_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_676_ = l_Lean_Options_empty;
v___x_677_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_677_, 0, v___x_671_);
lean_ctor_set(v___x_677_, 1, v___x_674_);
lean_ctor_set(v___x_677_, 2, v___x_675_);
lean_ctor_set(v___x_677_, 3, v___x_676_);
lean_inc(v_declHint_662_);
v___x_678_ = l_Lean_MessageData_ofConstName(v_declHint_662_, v___x_670_);
v_c_679_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_679_, 0, v___x_677_);
lean_ctor_set(v_c_679_, 1, v___x_678_);
v___x_680_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_666_, v_declHint_662_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
lean_dec_ref(v_env_666_);
lean_dec(v_declHint_662_);
v___x_681_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
lean_ctor_set(v___x_682_, 1, v_c_679_);
v___x_683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_682_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_MessageData_note(v___x_684_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v_msg_661_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_723_; 
v_val_688_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_723_ == 0)
{
v___x_690_ = v___x_680_;
v_isShared_691_ = v_isSharedCheck_723_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_val_688_);
lean_dec(v___x_680_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_723_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_mod_695_; uint8_t v___x_696_; 
v___x_692_ = lean_box(0);
v___x_693_ = l_Lean_Environment_header(v_env_666_);
lean_dec_ref(v_env_666_);
v___x_694_ = l_Lean_EnvironmentHeader_moduleNames(v___x_693_);
v_mod_695_ = lean_array_get(v___x_692_, v___x_694_, v_val_688_);
lean_dec(v_val_688_);
lean_dec_ref(v___x_694_);
v___x_696_ = l_Lean_isPrivateName(v_declHint_662_);
lean_dec(v_declHint_662_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v_c_679_);
v___x_699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = l_Lean_MessageData_ofName(v_mod_695_);
v___x_702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
v___x_703_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Lean_MessageData_note(v___x_704_);
v___x_706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_706_, 0, v_msg_661_);
lean_ctor_set(v___x_706_, 1, v___x_705_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 0);
lean_ctor_set(v___x_690_, 0, v___x_706_);
v___x_708_ = v___x_690_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_c_679_);
v___x_712_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_711_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = l_Lean_MessageData_ofName(v_mod_695_);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_MessageData_note(v___x_717_);
v___x_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_719_, 0, v_msg_661_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 0);
lean_ctor_set(v___x_690_, 0, v___x_719_);
v___x_721_ = v___x_690_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_727_, lean_object* v_declHint_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_727_, v_declHint_728_, v___y_729_);
lean_dec(v___y_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object* v_msg_732_, lean_object* v_declHint_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_752_; 
v___x_742_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_732_, v_declHint_733_, v___y_740_);
v_a_743_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_752_ == 0)
{
v___x_745_ = v___x_742_;
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_752_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_747_ = l_Lean_unknownIdentifierMessageTag;
v___x_748_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v_a_743_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 0, v___x_748_);
v___x_750_ = v___x_745_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_753_, lean_object* v_declHint_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_753_, v_declHint_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_ref_764_, lean_object* v_msg_765_, lean_object* v_declHint_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_){
_start:
{
lean_object* v___x_775_; lean_object* v_a_776_; lean_object* v___x_777_; 
v___x_775_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_765_, v_declHint_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v___x_777_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_764_, v_a_776_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_ref_778_, lean_object* v_msg_779_, lean_object* v_declHint_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_778_, v_msg_779_, v_declHint_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___y_781_);
lean_dec(v_ref_778_);
return v_res_789_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2));
v___x_795_ = l_Lean_stringToMessageData(v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_ref_796_, lean_object* v_constName_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_806_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_807_ = 0;
lean_inc(v_constName_797_);
v___x_808_ = l_Lean_MessageData_ofConstName(v_constName_797_, v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_796_, v___x_811_, v_constName_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_ref_813_, lean_object* v_constName_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_813_, v_constName_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec_ref(v___y_816_);
lean_dec(v___y_815_);
lean_dec(v_ref_813_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_ref_833_; lean_object* v___x_834_; 
v_ref_833_ = lean_ctor_get(v___y_830_, 5);
v___x_834_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_833_, v_constName_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec_ref(v___y_837_);
lean_dec(v___y_836_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object* v_constName_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___x_854_; lean_object* v_env_855_; uint8_t v___x_856_; lean_object* v___x_857_; 
v___x_854_ = lean_st_ref_get(v___y_852_);
v_env_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc_ref(v_env_855_);
lean_dec(v___x_854_);
v___x_856_ = 0;
lean_inc(v_constName_845_);
v___x_857_ = l_Lean_Environment_find_x3f(v_env_855_, v_constName_845_, v___x_856_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v___x_858_; 
v___x_858_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
return v___x_858_;
}
else
{
lean_object* v_val_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_dec(v_constName_845_);
v_val_859_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_857_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_val_859_);
lean_dec(v___x_857_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 0);
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_val_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object* v_constName_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
return v_res_876_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_instMonadEIO(lean_box(0));
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_toApplicative_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_957_; 
v___x_891_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0);
v___x_892_ = l_StateRefT_x27_instMonad___redArg(v___x_891_);
v_toApplicative_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v___x_892_, 1);
lean_dec(v_unused_958_);
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_957_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_toApplicative_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_957_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_toFunctor_897_; lean_object* v_toSeq_898_; lean_object* v_toSeqLeft_899_; lean_object* v_toSeqRight_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_955_; 
v_toFunctor_897_ = lean_ctor_get(v_toApplicative_893_, 0);
v_toSeq_898_ = lean_ctor_get(v_toApplicative_893_, 2);
v_toSeqLeft_899_ = lean_ctor_get(v_toApplicative_893_, 3);
v_toSeqRight_900_ = lean_ctor_get(v_toApplicative_893_, 4);
v_isSharedCheck_955_ = !lean_is_exclusive(v_toApplicative_893_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_toApplicative_893_, 1);
lean_dec(v_unused_956_);
v___x_902_ = v_toApplicative_893_;
v_isShared_903_ = v_isSharedCheck_955_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_toSeqRight_900_);
lean_inc(v_toSeqLeft_899_);
lean_inc(v_toSeq_898_);
lean_inc(v_toFunctor_897_);
lean_dec(v_toApplicative_893_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_955_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___f_904_; lean_object* v___f_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___f_910_; lean_object* v___f_911_; lean_object* v___x_913_; 
v___f_904_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1));
v___f_905_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_897_);
v___f_906_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_906_, 0, v_toFunctor_897_);
v___f_907_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_907_, 0, v_toFunctor_897_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___f_906_);
lean_ctor_set(v___x_908_, 1, v___f_907_);
v___f_909_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_909_, 0, v_toSeqRight_900_);
v___f_910_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_910_, 0, v_toSeqLeft_899_);
v___f_911_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_911_, 0, v_toSeq_898_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 4, v___f_909_);
lean_ctor_set(v___x_902_, 3, v___f_910_);
lean_ctor_set(v___x_902_, 2, v___f_911_);
lean_ctor_set(v___x_902_, 1, v___f_904_);
lean_ctor_set(v___x_902_, 0, v___x_908_);
v___x_913_ = v___x_902_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___f_904_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v___f_911_);
lean_ctor_set(v_reuseFailAlloc_954_, 3, v___f_910_);
lean_ctor_set(v_reuseFailAlloc_954_, 4, v___f_909_);
v___x_913_ = v_reuseFailAlloc_954_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_915_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v___f_905_);
lean_ctor_set(v___x_895_, 0, v___x_913_);
v___x_915_ = v___x_895_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v___f_905_);
v___x_915_ = v_reuseFailAlloc_953_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v_toApplicative_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_951_; 
v___x_916_ = l_StateRefT_x27_instMonad___redArg(v___x_915_);
v_toApplicative_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_916_, 1);
lean_dec(v_unused_952_);
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_951_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_toApplicative_917_);
lean_dec(v___x_916_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_951_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v_toFunctor_921_; lean_object* v_toSeq_922_; lean_object* v_toSeqLeft_923_; lean_object* v_toSeqRight_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_949_; 
v_toFunctor_921_ = lean_ctor_get(v_toApplicative_917_, 0);
v_toSeq_922_ = lean_ctor_get(v_toApplicative_917_, 2);
v_toSeqLeft_923_ = lean_ctor_get(v_toApplicative_917_, 3);
v_toSeqRight_924_ = lean_ctor_get(v_toApplicative_917_, 4);
v_isSharedCheck_949_ = !lean_is_exclusive(v_toApplicative_917_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v_toApplicative_917_, 1);
lean_dec(v_unused_950_);
v___x_926_ = v_toApplicative_917_;
v_isShared_927_ = v_isSharedCheck_949_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_toSeqRight_924_);
lean_inc(v_toSeqLeft_923_);
lean_inc(v_toSeq_922_);
lean_inc(v_toFunctor_921_);
lean_dec(v_toApplicative_917_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_949_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___f_933_; lean_object* v___f_934_; lean_object* v___f_935_; lean_object* v___x_937_; 
v___f_928_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3));
v___f_929_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_921_);
v___f_930_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_930_, 0, v_toFunctor_921_);
v___f_931_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_931_, 0, v_toFunctor_921_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___f_930_);
lean_ctor_set(v___x_932_, 1, v___f_931_);
v___f_933_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_933_, 0, v_toSeqRight_924_);
v___f_934_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_934_, 0, v_toSeqLeft_923_);
v___f_935_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_935_, 0, v_toSeq_922_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 4, v___f_933_);
lean_ctor_set(v___x_926_, 3, v___f_934_);
lean_ctor_set(v___x_926_, 2, v___f_935_);
lean_ctor_set(v___x_926_, 1, v___f_928_);
lean_ctor_set(v___x_926_, 0, v___x_932_);
v___x_937_ = v___x_926_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___f_928_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v___f_935_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v___f_934_);
lean_ctor_set(v_reuseFailAlloc_948_, 4, v___f_933_);
v___x_937_ = v_reuseFailAlloc_948_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 1, v___f_929_);
lean_ctor_set(v___x_919_, 0, v___x_937_);
v___x_939_ = v___x_919_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___f_929_);
v___x_939_ = v_reuseFailAlloc_947_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_13749__overap_945_; lean_object* v___x_946_; 
v___x_940_ = l_StateRefT_x27_instMonad___redArg(v___x_939_);
v___x_941_ = l_ReaderT_instMonad___redArg(v___x_940_);
v___x_942_ = l_ReaderT_instMonad___redArg(v___x_941_);
v___x_943_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_944_ = l_instInhabitedOfMonad___redArg(v___x_942_, v___x_943_);
v___x_13749__overap_945_ = lean_panic_fn_borrowed(v___x_944_, v_msg_882_);
lean_dec(v___x_944_);
lean_inc(v___y_889_);
lean_inc_ref(v___y_888_);
lean_inc(v___y_887_);
lean_inc_ref(v___y_886_);
lean_inc(v___y_885_);
lean_inc_ref(v___y_884_);
lean_inc(v___y_883_);
v___x_946_ = lean_apply_8(v___x_13749__overap_945_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, lean_box(0));
return v___x_946_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object* v_msg_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
return v_res_968_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_972_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2));
v___x_973_ = lean_unsigned_to_nat(53u);
v___x_974_ = lean_unsigned_to_nat(62u);
v___x_975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1));
v___x_976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0));
v___x_977_ = l_mkPanicMessageWithDecl(v___x_976_, v___x_975_, v___x_974_, v___x_973_, v___x_972_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t v_sz_978_, size_t v_i_979_, lean_object* v_bs_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v___x_989_; 
v___x_989_ = lean_usize_dec_lt(v_i_979_, v_sz_978_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; 
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v_bs_980_);
return v___x_990_;
}
else
{
lean_object* v_v_991_; lean_object* v___x_992_; 
v_v_991_ = lean_array_uget_borrowed(v_bs_980_, v_i_979_);
lean_inc(v_v_991_);
v___x_992_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_v_991_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v_a_993_; lean_object* v___x_994_; lean_object* v_bs_x27_995_; lean_object* v_a_997_; 
v_a_993_ = lean_ctor_get(v___x_992_, 0);
lean_inc(v_a_993_);
lean_dec_ref_known(v___x_992_, 1);
v___x_994_ = lean_unsigned_to_nat(0u);
v_bs_x27_995_ = lean_array_uset(v_bs_980_, v_i_979_, v___x_994_);
if (lean_obj_tag(v_a_993_) == 6)
{
lean_object* v_val_1002_; lean_object* v_numFields_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; 
v_val_1002_ = lean_ctor_get(v_a_993_, 0);
lean_inc_ref(v_val_1002_);
lean_dec_ref_known(v_a_993_, 1);
v_numFields_1003_ = lean_ctor_get(v_val_1002_, 4);
lean_inc(v_numFields_1003_);
lean_dec_ref(v_val_1002_);
v___x_1004_ = 0;
v___x_1005_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1005_, 0, v_numFields_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_994_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*2, v___x_1004_);
v_a_997_ = v___x_1005_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec(v_a_993_);
v___x_1006_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3);
v___x_1007_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v___x_1006_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v_a_997_ = v_a_1008_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_bs_x27_995_);
v_a_1009_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_1007_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1007_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
v___jp_996_:
{
size_t v___x_998_; size_t v___x_999_; lean_object* v___x_1000_; 
v___x_998_ = ((size_t)1ULL);
v___x_999_ = lean_usize_add(v_i_979_, v___x_998_);
v___x_1000_ = lean_array_uset(v_bs_x27_995_, v_i_979_, v_a_997_);
v_i_979_ = v___x_999_;
v_bs_980_ = v___x_1000_;
goto _start;
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref(v_bs_980_);
v_a_1017_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_992_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_992_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_bs_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
size_t v_sz_boxed_1036_; size_t v_i_boxed_1037_; lean_object* v_res_1038_; 
v_sz_boxed_1036_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_boxed_1036_, v_i_boxed_1037_, v_bs_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object* v_declName_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___x_1042_; lean_object* v_env_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_st_ref_get(v___y_1040_);
v_env_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc_ref(v_env_1043_);
lean_dec(v___x_1042_);
v___x_1044_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1043_, v_declName_1039_);
v___x_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object* v_declName_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1046_, v___y_1047_);
lean_dec(v___y_1047_);
return v_res_1049_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1050_; lean_object* v_dummy_1051_; 
v___x_1050_ = lean_box(0);
v_dummy_1051_ = l_Lean_Expr_sort___override(v___x_1050_);
return v_dummy_1051_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_box(0);
v___x_1053_ = lean_unsigned_to_nat(16u);
v___x_1054_ = lean_mk_array(v___x_1053_, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1055_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object* v_e_1060_, uint8_t v_alsoCasesOn_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = l_Lean_Expr_isApp(v_e_1060_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec_ref(v_e_1060_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Expr_getAppFn(v_e_1060_);
if (lean_obj_tag(v___x_1076_) == 4)
{
lean_object* v_declName_1077_; lean_object* v_us_1078_; lean_object* v___x_1079_; lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1234_; 
v_declName_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc_n(v_declName_1077_, 2);
v_us_1078_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_us_1078_);
lean_dec_ref_known(v___x_1076_, 2);
v___x_1079_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1077_, v___y_1068_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1082_ = v___x_1079_;
v_isShared_1083_ = v_isSharedCheck_1234_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1234_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
if (lean_obj_tag(v_a_1080_) == 1)
{
lean_object* v_val_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1126_; 
v_val_1084_ = lean_ctor_get(v_a_1080_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_a_1080_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1086_ = v_a_1080_;
v_isShared_1087_ = v_isSharedCheck_1126_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_val_1084_);
lean_dec(v_a_1080_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1126_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v_dummy_1088_; lean_object* v_nargs_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_args_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_dummy_1088_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_1089_ = l_Lean_Expr_getAppNumArgs(v_e_1060_);
lean_inc(v_nargs_1089_);
v___x_1090_ = lean_mk_array(v_nargs_1089_, v_dummy_1088_);
v___x_1091_ = lean_unsigned_to_nat(1u);
v___x_1092_ = lean_nat_sub(v_nargs_1089_, v___x_1091_);
lean_dec(v_nargs_1089_);
v_args_1093_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1060_, v___x_1090_, v___x_1092_);
v___x_1094_ = lean_array_get_size(v_args_1093_);
v___x_1095_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1084_);
v___x_1096_ = lean_nat_dec_lt(v___x_1094_, v___x_1095_);
lean_dec(v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v_numParams_1097_; lean_object* v_numDiscrs_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1117_; 
v_numParams_1097_ = lean_ctor_get(v_val_1084_, 0);
v_numDiscrs_1098_ = lean_ctor_get(v_val_1084_, 1);
v___x_1099_ = lean_array_mk(v_us_1078_);
v___x_1100_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1097_);
v___x_1101_ = l_Array_extract___redArg(v_args_1093_, v___x_1100_, v_numParams_1097_);
v___x_1102_ = l_Lean_instInhabitedExpr;
v___x_1103_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1084_);
v___x_1104_ = lean_array_get(v___x_1102_, v_args_1093_, v___x_1103_);
lean_dec(v___x_1103_);
v___x_1105_ = lean_nat_add(v_numParams_1097_, v___x_1091_);
v___x_1106_ = lean_nat_add(v___x_1105_, v_numDiscrs_1098_);
lean_inc(v___x_1106_);
lean_inc_ref_n(v_args_1093_, 2);
v___x_1107_ = l_Array_toSubarray___redArg(v_args_1093_, v___x_1105_, v___x_1106_);
v___x_1108_ = l_Subarray_copy___redArg(v___x_1107_);
v___x_1109_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1084_);
v___x_1110_ = lean_nat_add(v___x_1106_, v___x_1109_);
lean_dec(v___x_1109_);
lean_inc(v___x_1110_);
v___x_1111_ = l_Array_toSubarray___redArg(v_args_1093_, v___x_1106_, v___x_1110_);
v___x_1112_ = l_Subarray_copy___redArg(v___x_1111_);
v___x_1113_ = l_Array_toSubarray___redArg(v_args_1093_, v___x_1110_, v___x_1094_);
v___x_1114_ = l_Subarray_copy___redArg(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1115_, 0, v_val_1084_);
lean_ctor_set(v___x_1115_, 1, v_declName_1077_);
lean_ctor_set(v___x_1115_, 2, v___x_1099_);
lean_ctor_set(v___x_1115_, 3, v___x_1101_);
lean_ctor_set(v___x_1115_, 4, v___x_1104_);
lean_ctor_set(v___x_1115_, 5, v___x_1108_);
lean_ctor_set(v___x_1115_, 6, v___x_1112_);
lean_ctor_set(v___x_1115_, 7, v___x_1114_);
if (v_isShared_1087_ == 0)
{
lean_ctor_set(v___x_1086_, 0, v___x_1115_);
v___x_1117_ = v___x_1086_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1115_);
v___x_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1119_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1117_);
v___x_1119_ = v___x_1082_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
lean_dec_ref(v_args_1093_);
lean_del_object(v___x_1086_);
lean_dec(v_val_1084_);
lean_dec(v_us_1078_);
lean_dec(v_declName_1077_);
v___x_1122_ = lean_box(0);
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1122_);
v___x_1124_ = v___x_1082_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v___x_1127_; 
lean_del_object(v___x_1082_);
lean_dec(v_a_1080_);
v___x_1127_ = lean_st_ref_get(v___y_1068_);
if (v_alsoCasesOn_1061_ == 0)
{
lean_dec(v___x_1127_);
lean_dec(v_us_1078_);
lean_dec(v_declName_1077_);
lean_dec_ref(v_e_1060_);
goto v___jp_1070_;
}
else
{
lean_object* v_env_1128_; uint8_t v___x_1129_; 
v_env_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_env_1128_);
lean_dec(v___x_1127_);
lean_inc(v_declName_1077_);
v___x_1129_ = l_Lean_isCasesOnRecursor(v_env_1128_, v_declName_1077_);
if (v___x_1129_ == 0)
{
lean_dec(v_us_1078_);
lean_dec(v_declName_1077_);
lean_dec_ref(v_e_1060_);
goto v___jp_1070_;
}
else
{
lean_object* v_indName_1130_; lean_object* v___x_1131_; 
v_indName_1130_ = l_Lean_Name_getPrefix(v_declName_1077_);
v___x_1131_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_indName_1130_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1225_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1225_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1225_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
if (lean_obj_tag(v_a_1132_) == 5)
{
lean_object* v_val_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1220_; 
v_val_1136_ = lean_ctor_get(v_a_1132_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_a_1132_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1138_ = v_a_1132_;
v_isShared_1139_ = v_isSharedCheck_1220_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_val_1136_);
lean_dec(v_a_1132_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1220_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_toConstantVal_1140_; lean_object* v_numParams_1141_; lean_object* v_numIndices_1142_; lean_object* v_ctors_1143_; lean_object* v_nargs_1144_; lean_object* v_dummy_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v_args_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_toConstantVal_1140_ = lean_ctor_get(v_val_1136_, 0);
lean_inc_ref(v_toConstantVal_1140_);
v_numParams_1141_ = lean_ctor_get(v_val_1136_, 1);
lean_inc(v_numParams_1141_);
v_numIndices_1142_ = lean_ctor_get(v_val_1136_, 2);
lean_inc(v_numIndices_1142_);
v_ctors_1143_ = lean_ctor_get(v_val_1136_, 4);
lean_inc(v_ctors_1143_);
v_nargs_1144_ = l_Lean_Expr_getAppNumArgs(v_e_1060_);
v_dummy_1145_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
lean_inc(v_nargs_1144_);
v___x_1146_ = lean_mk_array(v_nargs_1144_, v_dummy_1145_);
v___x_1147_ = lean_unsigned_to_nat(1u);
v___x_1148_ = lean_nat_sub(v_nargs_1144_, v___x_1147_);
lean_dec(v_nargs_1144_);
v_args_1149_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1060_, v___x_1146_, v___x_1148_);
v___x_1150_ = lean_nat_add(v_numParams_1141_, v___x_1147_);
v___x_1151_ = lean_nat_add(v___x_1150_, v_numIndices_1142_);
v___x_1152_ = lean_nat_add(v___x_1151_, v___x_1147_);
lean_dec(v___x_1151_);
v___x_1153_ = l_Lean_InductiveVal_numCtors(v_val_1136_);
lean_dec_ref(v_val_1136_);
v___x_1154_ = lean_nat_add(v___x_1152_, v___x_1153_);
lean_dec(v___x_1153_);
v___x_1155_ = lean_array_get_size(v_args_1149_);
v___x_1156_ = lean_nat_dec_le(v___x_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_dec(v___x_1154_);
lean_dec(v___x_1152_);
lean_dec(v___x_1150_);
lean_dec_ref(v_args_1149_);
lean_dec(v_ctors_1143_);
lean_dec(v_numIndices_1142_);
lean_dec(v_numParams_1141_);
lean_dec_ref(v_toConstantVal_1140_);
lean_del_object(v___x_1138_);
lean_dec(v_us_1078_);
lean_dec(v_declName_1077_);
v___x_1157_ = lean_box(0);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1157_);
v___x_1159_ = v___x_1134_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
lean_object* v___x_1161_; lean_object* v_params_1162_; lean_object* v___x_1163_; lean_object* v_motive_1164_; lean_object* v_discrs_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v_discrInfos_1168_; lean_object* v_alts_1169_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v_lower_1211_; lean_object* v_upper_1212_; uint8_t v___x_1219_; 
lean_del_object(v___x_1134_);
v___x_1161_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1141_);
lean_inc_ref_n(v_args_1149_, 3);
v_params_1162_ = l_Array_toSubarray___redArg(v_args_1149_, v___x_1161_, v_numParams_1141_);
v___x_1163_ = l_Lean_instInhabitedExpr;
v_motive_1164_ = lean_array_get(v___x_1163_, v_args_1149_, v_numParams_1141_);
lean_dec(v_numParams_1141_);
lean_inc(v___x_1152_);
v_discrs_1165_ = l_Array_toSubarray___redArg(v_args_1149_, v___x_1150_, v___x_1152_);
v___x_1166_ = lean_nat_add(v_numIndices_1142_, v___x_1147_);
lean_dec(v_numIndices_1142_);
v___x_1167_ = lean_box(0);
v_discrInfos_1168_ = lean_mk_array(v___x_1166_, v___x_1167_);
lean_inc(v___x_1154_);
v_alts_1169_ = l_Array_toSubarray___redArg(v_args_1149_, v___x_1152_, v___x_1154_);
v___x_1219_ = lean_nat_dec_le(v___x_1154_, v___x_1161_);
if (v___x_1219_ == 0)
{
v_lower_1211_ = v___x_1154_;
v_upper_1212_ = v___x_1155_;
goto v___jp_1210_;
}
else
{
lean_dec(v___x_1154_);
v_lower_1211_ = v___x_1161_;
v_upper_1212_ = v___x_1155_;
goto v___jp_1210_;
}
v___jp_1170_:
{
lean_object* v___x_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1173_ = lean_array_mk(v_ctors_1143_);
v_sz_1174_ = lean_array_size(v___x_1173_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_1174_, v___x_1175_, v___x_1173_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1201_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1201_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1201_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_start_1181_; lean_object* v_stop_1182_; lean_object* v_start_1183_; lean_object* v_stop_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v_start_1181_ = lean_ctor_get(v_params_1162_, 1);
lean_inc(v_start_1181_);
v_stop_1182_ = lean_ctor_get(v_params_1162_, 2);
lean_inc(v_stop_1182_);
v_start_1183_ = lean_ctor_get(v_discrs_1165_, 1);
lean_inc(v_start_1183_);
v_stop_1184_ = lean_ctor_get(v_discrs_1165_, 2);
lean_inc(v_stop_1184_);
v___x_1185_ = lean_nat_sub(v_stop_1182_, v_start_1181_);
lean_dec(v_start_1181_);
lean_dec(v_stop_1182_);
v___x_1186_ = lean_nat_sub(v_stop_1184_, v_start_1183_);
lean_dec(v_start_1183_);
lean_dec(v_stop_1184_);
v___x_1187_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2);
v___x_1188_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1185_);
lean_ctor_set(v___x_1188_, 1, v___x_1186_);
lean_ctor_set(v___x_1188_, 2, v_a_1177_);
lean_ctor_set(v___x_1188_, 3, v___y_1172_);
lean_ctor_set(v___x_1188_, 4, v_discrInfos_1168_);
lean_ctor_set(v___x_1188_, 5, v___x_1187_);
v___x_1189_ = lean_array_mk(v_us_1078_);
v___x_1190_ = l_Subarray_copy___redArg(v_params_1162_);
v___x_1191_ = l_Subarray_copy___redArg(v_discrs_1165_);
v___x_1192_ = l_Subarray_copy___redArg(v_alts_1169_);
v___x_1193_ = l_Subarray_copy___redArg(v___y_1171_);
v___x_1194_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1188_);
lean_ctor_set(v___x_1194_, 1, v_declName_1077_);
lean_ctor_set(v___x_1194_, 2, v___x_1189_);
lean_ctor_set(v___x_1194_, 3, v___x_1190_);
lean_ctor_set(v___x_1194_, 4, v_motive_1164_);
lean_ctor_set(v___x_1194_, 5, v___x_1191_);
lean_ctor_set(v___x_1194_, 6, v___x_1192_);
lean_ctor_set(v___x_1194_, 7, v___x_1193_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set_tag(v___x_1138_, 1);
lean_ctor_set(v___x_1138_, 0, v___x_1194_);
v___x_1196_ = v___x_1138_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1196_);
v___x_1198_ = v___x_1179_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec_ref(v_alts_1169_);
lean_dec_ref(v_discrInfos_1168_);
lean_dec_ref(v_discrs_1165_);
lean_dec(v_motive_1164_);
lean_dec_ref(v_params_1162_);
lean_del_object(v___x_1138_);
lean_dec(v_us_1078_);
lean_dec(v_declName_1077_);
v_a_1202_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1176_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1176_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
v___jp_1210_:
{
lean_object* v_levelParams_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v_levelParams_1213_ = lean_ctor_get(v_toConstantVal_1140_, 1);
lean_inc(v_levelParams_1213_);
lean_dec_ref(v_toConstantVal_1140_);
v___x_1214_ = l_Array_toSubarray___redArg(v_args_1149_, v_lower_1211_, v_upper_1212_);
v___x_1215_ = l_List_lengthTR___redArg(v_levelParams_1213_);
lean_dec(v_levelParams_1213_);
v___x_1216_ = l_List_lengthTR___redArg(v_us_1078_);
v___x_1217_ = lean_nat_dec_eq(v___x_1215_, v___x_1216_);
lean_dec(v___x_1216_);
lean_dec(v___x_1215_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3));
v___y_1171_ = v___x_1214_;
v___y_1172_ = v___x_1218_;
goto v___jp_1170_;
}
else
{
v___y_1171_ = v___x_1214_;
v___y_1172_ = v___x_1167_;
goto v___jp_1170_;
}
}
}
}
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
lean_dec(v_a_1132_);
lean_dec(v_us_1078_);
lean_dec(v_declName_1077_);
lean_dec_ref(v_e_1060_);
v___x_1221_ = lean_box(0);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1221_);
v___x_1223_ = v___x_1134_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_us_1078_);
lean_dec(v_declName_1077_);
lean_dec_ref(v_e_1060_);
v_a_1226_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1131_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1131_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
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
lean_dec_ref(v___x_1076_);
lean_dec_ref(v_e_1060_);
goto v___jp_1070_;
}
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object* v_e_1235_, lean_object* v_alsoCasesOn_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1245_; lean_object* v_res_1246_; 
v_alsoCasesOn_boxed_1245_ = lean_unbox(v_alsoCasesOn_1236_);
v_res_1246_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1235_, v_alsoCasesOn_boxed_1245_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t v_sz_1247_, size_t v_i_1248_, lean_object* v_bs_1249_){
_start:
{
uint8_t v___x_1250_; 
v___x_1250_ = lean_usize_dec_lt(v_i_1248_, v_sz_1247_);
if (v___x_1250_ == 0)
{
return v_bs_1249_;
}
else
{
lean_object* v_v_1251_; lean_object* v___x_1252_; lean_object* v_bs_x27_1253_; lean_object* v___y_1255_; lean_object* v___x_1260_; 
v_v_1251_ = lean_array_uget(v_bs_1249_, v_i_1248_);
v___x_1252_ = lean_unsigned_to_nat(0u);
v_bs_x27_1253_ = lean_array_uset(v_bs_1249_, v_i_1248_, v___x_1252_);
v___x_1260_ = l_Lean_Elab_WF_isWfParam_x3f(v_v_1251_);
if (lean_obj_tag(v___x_1260_) == 0)
{
v___y_1255_ = v_v_1251_;
goto v___jp_1254_;
}
else
{
lean_object* v_val_1261_; 
lean_dec(v_v_1251_);
v_val_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_val_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v___y_1255_ = v_val_1261_;
goto v___jp_1254_;
}
v___jp_1254_:
{
size_t v___x_1256_; size_t v___x_1257_; lean_object* v___x_1258_; 
v___x_1256_ = ((size_t)1ULL);
v___x_1257_ = lean_usize_add(v_i_1248_, v___x_1256_);
v___x_1258_ = lean_array_uset(v_bs_x27_1253_, v_i_1248_, v___y_1255_);
v_i_1248_ = v___x_1257_;
v_bs_1249_ = v___x_1258_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object* v_sz_1262_, lean_object* v_i_1263_, lean_object* v_bs_1264_){
_start:
{
size_t v_sz_boxed_1265_; size_t v_i_boxed_1266_; lean_object* v_res_1267_; 
v_sz_boxed_1265_ = lean_unbox_usize(v_sz_1262_);
lean_dec(v_sz_1262_);
v_i_boxed_1266_ = lean_unbox_usize(v_i_1263_);
lean_dec(v_i_1263_);
v_res_1267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_boxed_1265_, v_i_boxed_1266_, v_bs_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object* v_as_1268_, size_t v_i_1269_, size_t v_stop_1270_){
_start:
{
uint8_t v___x_1271_; 
v___x_1271_ = lean_usize_dec_eq(v_i_1269_, v_stop_1270_);
if (v___x_1271_ == 0)
{
uint8_t v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = 1;
v___x_1273_ = lean_array_uget_borrowed(v_as_1268_, v_i_1269_);
v___x_1274_ = l_Lean_Elab_WF_isWfParam_x3f(v___x_1273_);
if (lean_obj_tag(v___x_1274_) == 0)
{
if (v___x_1271_ == 0)
{
size_t v___x_1275_; size_t v___x_1276_; 
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_add(v_i_1269_, v___x_1275_);
v_i_1269_ = v___x_1276_;
goto _start;
}
else
{
return v___x_1272_;
}
}
else
{
lean_dec_ref_known(v___x_1274_, 1);
return v___x_1272_;
}
}
else
{
uint8_t v___x_1278_; 
v___x_1278_ = 0;
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object* v_as_1279_, lean_object* v_i_1280_, lean_object* v_stop_1281_){
_start:
{
size_t v_i_boxed_1282_; size_t v_stop_boxed_1283_; uint8_t v_res_1284_; lean_object* v_r_1285_; 
v_i_boxed_1282_ = lean_unbox_usize(v_i_1280_);
lean_dec(v_i_1280_);
v_stop_boxed_1283_ = lean_unbox_usize(v_stop_1281_);
lean_dec(v_stop_1281_);
v_res_1284_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1279_, v_i_boxed_1282_, v_stop_boxed_1283_);
lean_dec_ref(v_as_1279_);
v_r_1285_ = lean_box(v_res_1284_);
return v_r_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher(lean_object* v_e_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
uint8_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = 1;
v___x_1296_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1286_, v___x_1295_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1359_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1359_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1359_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
if (lean_obj_tag(v_a_1297_) == 1)
{
lean_object* v_val_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1356_; 
v_val_1306_ = lean_ctor_get(v_a_1297_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_a_1297_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1308_ = v_a_1297_;
v_isShared_1309_ = v_isSharedCheck_1356_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_val_1306_);
lean_dec(v_a_1297_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1356_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v_toMatcherInfo_1310_; lean_object* v_matcherName_1311_; lean_object* v_matcherLevels_1312_; lean_object* v_params_1313_; lean_object* v_motive_1314_; lean_object* v_discrs_1315_; lean_object* v_alts_1316_; lean_object* v_remaining_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1355_; 
v_toMatcherInfo_1310_ = lean_ctor_get(v_val_1306_, 0);
v_matcherName_1311_ = lean_ctor_get(v_val_1306_, 1);
v_matcherLevels_1312_ = lean_ctor_get(v_val_1306_, 2);
v_params_1313_ = lean_ctor_get(v_val_1306_, 3);
v_motive_1314_ = lean_ctor_get(v_val_1306_, 4);
v_discrs_1315_ = lean_ctor_get(v_val_1306_, 5);
v_alts_1316_ = lean_ctor_get(v_val_1306_, 6);
v_remaining_1317_ = lean_ctor_get(v_val_1306_, 7);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_val_1306_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1319_ = v_val_1306_;
v_isShared_1320_ = v_isSharedCheck_1355_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_remaining_1317_);
lean_inc(v_alts_1316_);
lean_inc(v_discrs_1315_);
lean_inc(v_motive_1314_);
lean_inc(v_params_1313_);
lean_inc(v_matcherLevels_1312_);
lean_inc(v_matcherName_1311_);
lean_inc(v_toMatcherInfo_1310_);
lean_dec(v_val_1306_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1355_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v_discrs_1315_);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_del_object(v___x_1319_);
lean_dec_ref(v_remaining_1317_);
lean_dec_ref(v_alts_1316_);
lean_dec_ref(v_discrs_1315_);
lean_dec_ref(v_motive_1314_);
lean_dec_ref(v_params_1313_);
lean_dec_ref(v_matcherLevels_1312_);
lean_dec(v_matcherName_1311_);
lean_dec_ref(v_toMatcherInfo_1310_);
lean_del_object(v___x_1308_);
goto v___jp_1301_;
}
else
{
if (v___x_1323_ == 0)
{
lean_del_object(v___x_1319_);
lean_dec_ref(v_remaining_1317_);
lean_dec_ref(v_alts_1316_);
lean_dec_ref(v_discrs_1315_);
lean_dec_ref(v_motive_1314_);
lean_dec_ref(v_params_1313_);
lean_dec_ref(v_matcherLevels_1312_);
lean_dec(v_matcherName_1311_);
lean_dec_ref(v_toMatcherInfo_1310_);
lean_del_object(v___x_1308_);
goto v___jp_1301_;
}
else
{
size_t v___x_1324_; size_t v___x_1325_; uint8_t v___x_1326_; 
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lean_usize_of_nat(v___x_1322_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_discrs_1315_, v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_del_object(v___x_1319_);
lean_dec_ref(v_remaining_1317_);
lean_dec_ref(v_alts_1316_);
lean_dec_ref(v_discrs_1315_);
lean_dec_ref(v_motive_1314_);
lean_dec_ref(v_params_1313_);
lean_dec_ref(v_matcherLevels_1312_);
lean_dec(v_matcherName_1311_);
lean_dec_ref(v_toMatcherInfo_1310_);
lean_del_object(v___x_1308_);
goto v___jp_1301_;
}
else
{
size_t v_sz_1327_; lean_object* v___x_1328_; 
lean_del_object(v___x_1299_);
v_sz_1327_ = lean_array_size(v_alts_1316_);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_1327_, v___x_1324_, v_alts_1316_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1346_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1331_ = v___x_1328_;
v_isShared_1332_ = v_isSharedCheck_1346_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1328_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1346_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
size_t v_sz_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; 
v_sz_1333_ = lean_array_size(v_discrs_1315_);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1333_, v___x_1324_, v_discrs_1315_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 6, v_a_1329_);
lean_ctor_set(v___x_1319_, 5, v___x_1334_);
v___x_1336_ = v___x_1319_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_toMatcherInfo_1310_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_matcherName_1311_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_matcherLevels_1312_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v_params_1313_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v_motive_1314_);
lean_ctor_set(v_reuseFailAlloc_1345_, 5, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1345_, 6, v_a_1329_);
lean_ctor_set(v_reuseFailAlloc_1345_, 7, v_remaining_1317_);
v___x_1336_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
v___x_1337_ = l_Lean_Meta_MatcherApp_toExpr(v___x_1336_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1337_);
v___x_1339_ = v___x_1308_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
if (v_isShared_1332_ == 0)
{
lean_ctor_set(v___x_1331_, 0, v___x_1340_);
v___x_1342_ = v___x_1331_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_del_object(v___x_1319_);
lean_dec_ref(v_remaining_1317_);
lean_dec_ref(v_discrs_1315_);
lean_dec_ref(v_motive_1314_);
lean_dec_ref(v_params_1313_);
lean_dec_ref(v_matcherLevels_1312_);
lean_dec(v_matcherName_1311_);
lean_dec_ref(v_toMatcherInfo_1310_);
lean_del_object(v___x_1308_);
v_a_1347_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1328_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1328_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
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
lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_del_object(v___x_1299_);
lean_dec(v_a_1297_);
v___x_1357_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
v___jp_1301_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1302_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
v_a_1360_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1296_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1296_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object* v_e_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Elab_WF_paramMatcher(v_e_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t v_sz_1378_, size_t v_i_1379_, lean_object* v_bs_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1378_, v_i_1379_, v_bs_1380_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object* v_sz_1390_, lean_object* v_i_1391_, lean_object* v_bs_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
size_t v_sz_boxed_1401_; size_t v_i_boxed_1402_; lean_object* v_res_1403_; 
v_sz_boxed_1401_ = lean_unbox_usize(v_sz_1390_);
lean_dec(v_sz_1390_);
v_i_boxed_1402_ = lean_unbox_usize(v_i_1391_);
lean_dec(v_i_1391_);
v_res_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_boxed_1401_, v_i_boxed_1402_, v_bs_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object* v_declName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1404_, v___y_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object* v_declName_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_1424_, lean_object* v_constName_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_constName_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(v_00_u03b1_1435_, v_constName_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v___y_1439_);
lean_dec_ref(v___y_1438_);
lean_dec(v___y_1437_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b1_1446_, lean_object* v_ref_1447_, lean_object* v_constName_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_1447_, v_constName_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b1_1458_, lean_object* v_ref_1459_, lean_object* v_constName_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(v_00_u03b1_1458_, v_ref_1459_, v_constName_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec(v_ref_1459_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_1470_, lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v_declHint_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_1471_, v_msg_1472_, v_declHint_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1483_, lean_object* v_ref_1484_, lean_object* v_msg_1485_, lean_object* v_declHint_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_1483_, v_ref_1484_, v_msg_1485_, v_declHint_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec(v_ref_1484_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1496_, lean_object* v_declHint_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1496_, v_declHint_1497_, v___y_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1507_, lean_object* v_declHint_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1507_, v_declHint_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1518_, lean_object* v_ref_1519_, lean_object* v_msg_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_1519_, v_msg_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1530_, lean_object* v_ref_1531_, lean_object* v_msg_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(v_00_u03b1_1530_, v_ref_1531_, v_msg_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec(v_ref_1531_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_1542_, lean_object* v_msg_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_1543_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1553_, lean_object* v_msg_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(v_00_u03b1_1553_, v_msg_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1571_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1572_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1573_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1574_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1571_, v___x_1572_, v___x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12____boxed(lean_object* v_a_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
return v_res_1576_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1580_; uint8_t v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1580_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1581_ = 1;
v___x_1582_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14__once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_);
v___x_1583_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1580_, v___x_1581_, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14____boxed(lean_object* v_a_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
return v_res_1585_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object* v_e_1586_){
_start:
{
if (lean_obj_tag(v_e_1586_) == 8)
{
lean_object* v_value_1587_; lean_object* v_body_1588_; lean_object* v___x_1589_; 
v_value_1587_ = lean_ctor_get(v_e_1586_, 2);
v_body_1588_ = lean_ctor_get(v_e_1586_, 3);
v___x_1589_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1587_);
if (lean_obj_tag(v___x_1589_) == 0)
{
v_e_1586_ = v_body_1588_;
goto _start;
}
else
{
uint8_t v___x_1591_; 
lean_dec_ref_known(v___x_1589_, 1);
v___x_1591_ = 1;
return v___x_1591_;
}
}
else
{
uint8_t v___x_1592_; 
v___x_1592_ = 0;
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object* v_e_1593_){
_start:
{
uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_res_1594_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1593_);
lean_dec_ref(v_e_1593_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object* v_e_1596_, lean_object* v_acc_1597_){
_start:
{
if (lean_obj_tag(v_e_1596_) == 8)
{
lean_object* v_value_1598_; lean_object* v_body_1599_; lean_object* v___x_1600_; 
v_value_1598_ = lean_ctor_get(v_e_1596_, 2);
v_body_1599_ = lean_ctor_get(v_e_1596_, 3);
v___x_1600_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1598_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_unsigned_to_nat(1u);
v___x_1602_ = lean_nat_add(v_acc_1597_, v___x_1601_);
lean_dec(v_acc_1597_);
v_e_1596_ = v_body_1599_;
v_acc_1597_ = v___x_1602_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1600_, 1);
return v_acc_1597_;
}
}
else
{
return v_acc_1597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object* v_e_1604_, lean_object* v_acc_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1604_, v_acc_1605_);
lean_dec_ref(v_e_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object* v_msg_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1300__overap_1615_; lean_object* v___x_1616_; 
v___f_1614_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0));
v___x_1300__overap_1615_ = lean_panic_fn_borrowed(v___f_1614_, v_msg_1608_);
lean_inc(v___y_1612_);
lean_inc_ref(v___y_1611_);
lean_inc(v___y_1610_);
lean_inc_ref(v___y_1609_);
v___x_1616_ = lean_apply_5(v___x_1300__overap_1615_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, lean_box(0));
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object* v_msg_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object* v_k_1624_, lean_object* v_b_1625_, lean_object* v_c_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v___x_1632_; 
lean_inc(v___y_1630_);
lean_inc_ref(v___y_1629_);
lean_inc(v___y_1628_);
lean_inc_ref(v___y_1627_);
v___x_1632_ = lean_apply_7(v_k_1624_, v_b_1625_, v_c_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, lean_box(0));
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object* v_k_1633_, lean_object* v_b_1634_, lean_object* v_c_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1633_, v_b_1634_, v_c_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object* v_e_1642_, lean_object* v_maxFVars_x3f_1643_, lean_object* v_k_1644_, uint8_t v_cleanupAnnotations_1645_, uint8_t v_preserveNondepLet_1646_, uint8_t v_nondepLetOnly_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___f_1653_; uint8_t v___x_1654_; uint8_t v___x_1655_; lean_object* v___x_1656_; 
v___f_1653_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1653_, 0, v_k_1644_);
v___x_1654_ = 0;
v___x_1655_ = 1;
v___x_1656_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1642_, v___x_1654_, v___x_1655_, v_preserveNondepLet_1646_, v_nondepLetOnly_1647_, v_maxFVars_x3f_1643_, v___f_1653_, v_cleanupAnnotations_1645_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1656_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1656_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
v_a_1665_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1656_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1656_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object* v_e_1673_, lean_object* v_maxFVars_x3f_1674_, lean_object* v_k_1675_, lean_object* v_cleanupAnnotations_1676_, lean_object* v_preserveNondepLet_1677_, lean_object* v_nondepLetOnly_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1684_; uint8_t v_preserveNondepLet_boxed_1685_; uint8_t v_nondepLetOnly_boxed_1686_; lean_object* v_res_1687_; 
v_cleanupAnnotations_boxed_1684_ = lean_unbox(v_cleanupAnnotations_1676_);
v_preserveNondepLet_boxed_1685_ = lean_unbox(v_preserveNondepLet_1677_);
v_nondepLetOnly_boxed_1686_ = lean_unbox(v_nondepLetOnly_1678_);
v_res_1687_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1673_, v_maxFVars_x3f_1674_, v_k_1675_, v_cleanupAnnotations_boxed_1684_, v_preserveNondepLet_boxed_1685_, v_nondepLetOnly_boxed_1686_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_maxFVars_x3f_1674_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object* v_00_u03b1_1688_, lean_object* v_e_1689_, lean_object* v_maxFVars_x3f_1690_, lean_object* v_k_1691_, uint8_t v_cleanupAnnotations_1692_, uint8_t v_preserveNondepLet_1693_, uint8_t v_nondepLetOnly_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1689_, v_maxFVars_x3f_1690_, v_k_1691_, v_cleanupAnnotations_1692_, v_preserveNondepLet_1693_, v_nondepLetOnly_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object* v_00_u03b1_1701_, lean_object* v_e_1702_, lean_object* v_maxFVars_x3f_1703_, lean_object* v_k_1704_, lean_object* v_cleanupAnnotations_1705_, lean_object* v_preserveNondepLet_1706_, lean_object* v_nondepLetOnly_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1713_; uint8_t v_preserveNondepLet_boxed_1714_; uint8_t v_nondepLetOnly_boxed_1715_; lean_object* v_res_1716_; 
v_cleanupAnnotations_boxed_1713_ = lean_unbox(v_cleanupAnnotations_1705_);
v_preserveNondepLet_boxed_1714_ = lean_unbox(v_preserveNondepLet_1706_);
v_nondepLetOnly_boxed_1715_ = lean_unbox(v_nondepLetOnly_1707_);
v_res_1716_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(v_00_u03b1_1701_, v_e_1702_, v_maxFVars_x3f_1703_, v_k_1704_, v_cleanupAnnotations_boxed_1713_, v_preserveNondepLet_boxed_1714_, v_nondepLetOnly_boxed_1715_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v_maxFVars_x3f_1703_);
return v_res_1716_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = l_Lean_Expr_bvar___override(v___x_1717_);
return v___x_1718_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4(void){
_start:
{
lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1722_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3));
v___x_1723_ = lean_unsigned_to_nat(6u);
v___x_1724_ = lean_unsigned_to_nat(142u);
v___x_1725_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2));
v___x_1726_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1));
v___x_1727_ = l_mkPanicMessageWithDecl(v___x_1726_, v___x_1725_, v___x_1724_, v___x_1723_, v___x_1722_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object* v_xs_1728_, lean_object* v_b_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1728_, v_b_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec_ref(v_xs_1728_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object* v_e_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
if (lean_obj_tag(v_e_1736_) == 8)
{
lean_object* v_declName_1742_; lean_object* v_type_1743_; lean_object* v_value_1744_; lean_object* v_body_1745_; uint8_t v_nondep_1746_; lean_object* v___x_1747_; 
v_declName_1742_ = lean_ctor_get(v_e_1736_, 0);
v_type_1743_ = lean_ctor_get(v_e_1736_, 1);
v_value_1744_ = lean_ctor_get(v_e_1736_, 2);
v_body_1745_ = lean_ctor_get(v_e_1736_, 3);
v_nondep_1746_ = lean_ctor_get_uint8(v_e_1736_, sizeof(void*)*4 + 8);
v___x_1747_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1744_);
if (lean_obj_tag(v___x_1747_) == 1)
{
lean_object* v_val_1748_; lean_object* v___x_1749_; 
v_val_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v___x_1747_, 1);
lean_inc_ref(v_type_1743_);
v___x_1749_ = l_Lean_Meta_isProp(v_type_1743_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; uint8_t v___y_1752_; uint8_t v___x_1760_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1760_ = lean_unbox(v_a_1750_);
lean_dec(v_a_1750_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_inc_ref(v_type_1743_);
v___x_1761_ = l_Lean_Meta_getLevel(v_type_1743_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___y_1771_; size_t v___x_1780_; uint8_t v___x_1781_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
v___x_1763_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_a_1762_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = l_Lean_Expr_const___override(v___x_1763_, v___x_1765_);
v___x_1767_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0);
lean_inc_ref(v_type_1743_);
v___x_1768_ = l_Lean_mkAppB(v___x_1766_, v_type_1743_, v___x_1767_);
v___x_1769_ = lean_expr_instantiate1(v_body_1745_, v___x_1768_);
lean_dec_ref(v___x_1768_);
v___x_1780_ = lean_ptr_addr(v_type_1743_);
v___x_1781_ = lean_usize_dec_eq(v___x_1780_, v___x_1780_);
if (v___x_1781_ == 0)
{
v___y_1771_ = v___x_1781_;
goto v___jp_1770_;
}
else
{
size_t v___x_1782_; size_t v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = lean_ptr_addr(v_value_1744_);
v___x_1783_ = lean_ptr_addr(v_val_1748_);
v___x_1784_ = lean_usize_dec_eq(v___x_1782_, v___x_1783_);
v___y_1771_ = v___x_1784_;
goto v___jp_1770_;
}
v___jp_1770_:
{
if (v___y_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_inc_ref(v_type_1743_);
lean_inc(v_declName_1742_);
lean_dec_ref_known(v_e_1736_, 4);
v___x_1772_ = l_Lean_Expr_letE___override(v_declName_1742_, v_type_1743_, v_val_1748_, v___x_1769_, v_nondep_1746_);
v_e_1736_ = v___x_1772_;
goto _start;
}
else
{
size_t v___x_1774_; size_t v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = lean_ptr_addr(v_body_1745_);
v___x_1775_ = lean_ptr_addr(v___x_1769_);
v___x_1776_ = lean_usize_dec_eq(v___x_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; 
lean_inc_ref(v_type_1743_);
lean_inc(v_declName_1742_);
lean_dec_ref_known(v_e_1736_, 4);
v___x_1777_ = l_Lean_Expr_letE___override(v_declName_1742_, v_type_1743_, v_val_1748_, v___x_1769_, v_nondep_1746_);
v_e_1736_ = v___x_1777_;
goto _start;
}
else
{
lean_dec_ref(v___x_1769_);
lean_dec(v_val_1748_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v_val_1748_);
lean_dec_ref_known(v_e_1736_, 4);
v_a_1785_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1761_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1761_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
else
{
size_t v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = lean_ptr_addr(v_type_1743_);
v___x_1794_ = lean_usize_dec_eq(v___x_1793_, v___x_1793_);
if (v___x_1794_ == 0)
{
v___y_1752_ = v___x_1794_;
goto v___jp_1751_;
}
else
{
size_t v___x_1795_; size_t v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_ptr_addr(v_value_1744_);
v___x_1796_ = lean_ptr_addr(v_val_1748_);
v___x_1797_ = lean_usize_dec_eq(v___x_1795_, v___x_1796_);
v___y_1752_ = v___x_1797_;
goto v___jp_1751_;
}
}
v___jp_1751_:
{
if (v___y_1752_ == 0)
{
lean_object* v___x_1753_; 
lean_inc_ref(v_body_1745_);
lean_inc_ref(v_type_1743_);
lean_inc(v_declName_1742_);
lean_dec_ref_known(v_e_1736_, 4);
v___x_1753_ = l_Lean_Expr_letE___override(v_declName_1742_, v_type_1743_, v_val_1748_, v_body_1745_, v_nondep_1746_);
v_e_1736_ = v___x_1753_;
goto _start;
}
else
{
size_t v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_ptr_addr(v_body_1745_);
v___x_1756_ = lean_usize_dec_eq(v___x_1755_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_inc_ref(v_body_1745_);
lean_inc_ref(v_type_1743_);
lean_inc(v_declName_1742_);
lean_dec_ref_known(v_e_1736_, 4);
v___x_1757_ = l_Lean_Expr_letE___override(v_declName_1742_, v_type_1743_, v_val_1748_, v_body_1745_, v_nondep_1746_);
v_e_1736_ = v___x_1757_;
goto _start;
}
else
{
lean_dec(v_val_1748_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_val_1748_);
lean_dec_ref_known(v_e_1736_, 4);
v_a_1798_ = lean_ctor_get(v___x_1749_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1749_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1749_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1749_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v___x_1806_; lean_object* v_num_1807_; uint8_t v___x_1808_; 
lean_dec(v___x_1747_);
v___x_1806_ = lean_unsigned_to_nat(0u);
v_num_1807_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1736_, v___x_1806_);
v___x_1808_ = lean_nat_dec_lt(v___x_1806_, v_num_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
lean_dec(v_num_1807_);
lean_dec_ref_known(v_e_1736_, 4);
v___x_1809_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4);
v___x_1810_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v___x_1809_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1810_;
}
else
{
lean_object* v___f_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; lean_object* v___x_1814_; 
v___f_1811_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed), 7, 0);
v___x_1812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1812_, 0, v_num_1807_);
v___x_1813_ = 0;
v___x_1814_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1736_, v___x_1812_, v___f_1811_, v___x_1813_, v___x_1808_, v___x_1813_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
lean_dec_ref_known(v___x_1812_, 1);
return v___x_1814_;
}
}
}
else
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_e_1736_);
return v___x_1815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object* v_xs_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_b_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; uint8_t v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref_known(v___x_1823_, 1);
v___x_1825_ = 0;
v___x_1826_ = 1;
v___x_1827_ = l_Lean_Meta_mkLetFVars(v_xs_1816_, v_a_1824_, v___x_1825_, v___x_1825_, v___x_1826_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
return v___x_1827_;
}
else
{
return v___x_1823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object* v_e_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
uint8_t v___y_1842_; uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_Expr_isLet(v_e_1835_);
if (v___x_1864_ == 0)
{
uint8_t v___x_1865_; 
v___x_1865_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1835_);
v___y_1842_ = v___x_1865_;
goto v___jp_1841_;
}
else
{
v___y_1842_ = v___x_1864_;
goto v___jp_1841_;
}
v___jp_1841_:
{
if (v___y_1842_ == 0)
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec_ref(v_e_1835_);
v___x_1843_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
else
{
lean_object* v___x_1845_; 
v___x_1845_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1855_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1855_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_a_1846_);
v___x_1851_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1851_);
v___x_1853_ = v___x_1848_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_a_1856_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1845_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1845_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object* v_e_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet(lean_object* v_e_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1873_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object* v_e_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_Elab_WF_paramLet(v_e_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
lean_dec(v_a_1890_);
lean_dec_ref(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
lean_dec(v_a_1886_);
lean_dec_ref(v_a_1885_);
lean_dec(v_a_1884_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1901_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1902_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1903_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1900_, v___x_1901_, v___x_1902_);
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12____boxed(lean_object* v_a_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
return v_res_1905_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1910_ = 1;
v___x_1911_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14__once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_);
v___x_1912_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1909_, v___x_1910_, v___x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14____boxed(lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object* v_lctx_1915_, lean_object* v_x_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_keyedConfig_1922_; uint8_t v_trackZetaDelta_1923_; lean_object* v_zetaDeltaSet_1924_; lean_object* v_localInstances_1925_; lean_object* v_defEqCtx_x3f_1926_; lean_object* v_synthPendingDepth_1927_; lean_object* v_canUnfold_x3f_1928_; uint8_t v_univApprox_1929_; uint8_t v_inTypeClassResolution_1930_; uint8_t v_cacheInferType_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_keyedConfig_1922_ = lean_ctor_get(v___y_1917_, 0);
v_trackZetaDelta_1923_ = lean_ctor_get_uint8(v___y_1917_, sizeof(void*)*7);
v_zetaDeltaSet_1924_ = lean_ctor_get(v___y_1917_, 1);
v_localInstances_1925_ = lean_ctor_get(v___y_1917_, 3);
v_defEqCtx_x3f_1926_ = lean_ctor_get(v___y_1917_, 4);
v_synthPendingDepth_1927_ = lean_ctor_get(v___y_1917_, 5);
v_canUnfold_x3f_1928_ = lean_ctor_get(v___y_1917_, 6);
v_univApprox_1929_ = lean_ctor_get_uint8(v___y_1917_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1930_ = lean_ctor_get_uint8(v___y_1917_, sizeof(void*)*7 + 2);
v_cacheInferType_1931_ = lean_ctor_get_uint8(v___y_1917_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1928_);
lean_inc(v_synthPendingDepth_1927_);
lean_inc(v_defEqCtx_x3f_1926_);
lean_inc_ref(v_localInstances_1925_);
lean_inc(v_zetaDeltaSet_1924_);
lean_inc_ref(v_keyedConfig_1922_);
v___x_1932_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1932_, 0, v_keyedConfig_1922_);
lean_ctor_set(v___x_1932_, 1, v_zetaDeltaSet_1924_);
lean_ctor_set(v___x_1932_, 2, v_lctx_1915_);
lean_ctor_set(v___x_1932_, 3, v_localInstances_1925_);
lean_ctor_set(v___x_1932_, 4, v_defEqCtx_x3f_1926_);
lean_ctor_set(v___x_1932_, 5, v_synthPendingDepth_1927_);
lean_ctor_set(v___x_1932_, 6, v_canUnfold_x3f_1928_);
lean_ctor_set_uint8(v___x_1932_, sizeof(void*)*7, v_trackZetaDelta_1923_);
lean_ctor_set_uint8(v___x_1932_, sizeof(void*)*7 + 1, v_univApprox_1929_);
lean_ctor_set_uint8(v___x_1932_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1930_);
lean_ctor_set_uint8(v___x_1932_, sizeof(void*)*7 + 3, v_cacheInferType_1931_);
lean_inc(v___y_1920_);
lean_inc_ref(v___y_1919_);
lean_inc(v___y_1918_);
v___x_1933_ = lean_apply_5(v_x_1916_, v___x_1932_, v___y_1918_, v___y_1919_, v___y_1920_, lean_box(0));
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object* v_lctx_1934_, lean_object* v_x_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1934_, v_x_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object* v_00_u03b1_1942_, lean_object* v_lctx_1943_, lean_object* v_x_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1943_, v_x_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object* v_00_u03b1_1951_, lean_object* v_lctx_1952_, lean_object* v_x_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(v_00_u03b1_1951_, v_lctx_1952_, v_x_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object* v_e_1960_, lean_object* v_k_1961_, uint8_t v_cleanupAnnotations_1962_, uint8_t v_preserveNondepLet_1963_, uint8_t v_nondepLetOnly_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v___f_1970_; uint8_t v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___f_1970_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1970_, 0, v_k_1961_);
v___x_1971_ = 0;
v___x_1972_ = 1;
v___x_1973_ = lean_box(0);
v___x_1974_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1960_, v___x_1971_, v___x_1972_, v_preserveNondepLet_1963_, v_nondepLetOnly_1964_, v___x_1973_, v___f_1970_, v_cleanupAnnotations_1962_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1974_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1974_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
v_a_1983_ = lean_ctor_get(v___x_1974_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1974_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1974_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1974_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object* v_e_1991_, lean_object* v_k_1992_, lean_object* v_cleanupAnnotations_1993_, lean_object* v_preserveNondepLet_1994_, lean_object* v_nondepLetOnly_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2001_; uint8_t v_preserveNondepLet_boxed_2002_; uint8_t v_nondepLetOnly_boxed_2003_; lean_object* v_res_2004_; 
v_cleanupAnnotations_boxed_2001_ = lean_unbox(v_cleanupAnnotations_1993_);
v_preserveNondepLet_boxed_2002_ = lean_unbox(v_preserveNondepLet_1994_);
v_nondepLetOnly_boxed_2003_ = lean_unbox(v_nondepLetOnly_1995_);
v_res_2004_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_1991_, v_k_1992_, v_cleanupAnnotations_boxed_2001_, v_preserveNondepLet_boxed_2002_, v_nondepLetOnly_boxed_2003_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object* v_00_u03b1_2005_, lean_object* v_e_2006_, lean_object* v_k_2007_, uint8_t v_cleanupAnnotations_2008_, uint8_t v_preserveNondepLet_2009_, uint8_t v_nondepLetOnly_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; 
v___x_2016_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2006_, v_k_2007_, v_cleanupAnnotations_2008_, v_preserveNondepLet_2009_, v_nondepLetOnly_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object* v_00_u03b1_2017_, lean_object* v_e_2018_, lean_object* v_k_2019_, lean_object* v_cleanupAnnotations_2020_, lean_object* v_preserveNondepLet_2021_, lean_object* v_nondepLetOnly_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2028_; uint8_t v_preserveNondepLet_boxed_2029_; uint8_t v_nondepLetOnly_boxed_2030_; lean_object* v_res_2031_; 
v_cleanupAnnotations_boxed_2028_ = lean_unbox(v_cleanupAnnotations_2020_);
v_preserveNondepLet_boxed_2029_ = lean_unbox(v_preserveNondepLet_2021_);
v_nondepLetOnly_boxed_2030_ = lean_unbox(v_nondepLetOnly_2022_);
v_res_2031_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(v_00_u03b1_2017_, v_e_2018_, v_k_2019_, v_cleanupAnnotations_boxed_2028_, v_preserveNondepLet_boxed_2029_, v_nondepLetOnly_boxed_2030_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object* v_e_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2038_, 0, v_e_2032_);
v___x_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object* v_e_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object* v_as_2047_, size_t v_i_2048_, size_t v_stop_2049_, lean_object* v_b_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
uint8_t v___x_2056_; 
v___x_2056_ = lean_usize_dec_eq(v_i_2048_, v_stop_2049_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = lean_array_uget_borrowed(v_as_2047_, v_i_2048_);
v___x_2058_ = l_Lean_Expr_fvarId_x21(v___x_2057_);
v___x_2059_ = l_Lean_FVarId_getDecl___redArg(v___x_2058_, v___y_2051_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2059_) == 0)
{
lean_object* v_a_2060_; uint8_t v_a_2062_; uint8_t v___x_2068_; 
v_a_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_a_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v___x_2068_ = l_Lean_LocalDecl_isNondep(v_a_2060_);
if (v___x_2068_ == 0)
{
v_a_2062_ = v___x_2068_;
goto v___jp_2061_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = l_Lean_LocalDecl_type(v_a_2060_);
v___x_2070_ = l_Lean_Meta_isProp(v___x_2069_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; uint8_t v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = lean_unbox(v_a_2071_);
lean_dec(v_a_2071_);
v_a_2062_ = v___x_2072_;
goto v___jp_2061_;
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec(v_a_2060_);
lean_dec_ref(v_b_2050_);
v_a_2073_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2070_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2070_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
v___jp_2061_:
{
lean_object* v___x_2063_; lean_object* v___x_2064_; size_t v___x_2065_; size_t v___x_2066_; 
v___x_2063_ = l_Lean_LocalDecl_setNondep(v_a_2060_, v_a_2062_);
v___x_2064_ = l_Lean_LocalContext_addDecl(v_b_2050_, v___x_2063_);
v___x_2065_ = ((size_t)1ULL);
v___x_2066_ = lean_usize_add(v_i_2048_, v___x_2065_);
v_i_2048_ = v___x_2066_;
v_b_2050_ = v___x_2064_;
goto _start;
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v_b_2050_);
v_a_2081_ = lean_ctor_get(v___x_2059_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2059_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2059_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_b_2050_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object* v_as_2090_, lean_object* v_i_2091_, lean_object* v_stop_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
size_t v_i_boxed_2099_; size_t v_stop_boxed_2100_; lean_object* v_res_2101_; 
v_i_boxed_2099_ = lean_unbox_usize(v_i_2091_);
lean_dec(v_i_2091_);
v_stop_boxed_2100_ = lean_unbox_usize(v_stop_2092_);
lean_dec(v_stop_2092_);
v_res_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2090_, v_i_boxed_2099_, v_stop_boxed_2100_, v_b_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec_ref(v_as_2090_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t v_a_2102_, lean_object* v_lctx_2103_, lean_object* v_xs_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_a_2112_; lean_object* v___y_2120_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_array_get_size(v_xs_2104_);
v___x_2132_ = lean_nat_dec_lt(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
v_a_2112_ = v_lctx_2103_;
goto v___jp_2111_;
}
else
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_nat_dec_le(v___x_2131_, v___x_2131_);
if (v___x_2133_ == 0)
{
if (v___x_2132_ == 0)
{
v_a_2112_ = v_lctx_2103_;
goto v___jp_2111_;
}
else
{
size_t v___x_2134_; size_t v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = ((size_t)0ULL);
v___x_2135_ = lean_usize_of_nat(v___x_2131_);
v___x_2136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2104_, v___x_2134_, v___x_2135_, v_lctx_2103_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
v___y_2120_ = v___x_2136_;
goto v___jp_2119_;
}
}
else
{
size_t v___x_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = lean_usize_of_nat(v___x_2131_);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2104_, v___x_2137_, v___x_2138_, v_lctx_2103_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
v___y_2120_ = v___x_2139_;
goto v___jp_2119_;
}
}
v___jp_2111_:
{
uint8_t v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2113_ = 1;
v___x_2114_ = lean_box(v_a_2102_);
v___x_2115_ = lean_box(v_a_2102_);
v___x_2116_ = lean_box(v___x_2113_);
v___x_2117_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2117_, 0, v_xs_2104_);
lean_closure_set(v___x_2117_, 1, v_b_2105_);
lean_closure_set(v___x_2117_, 2, v___x_2114_);
lean_closure_set(v___x_2117_, 3, v___x_2115_);
lean_closure_set(v___x_2117_, 4, v___x_2116_);
v___x_2118_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_a_2112_, v___x_2117_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
return v___x_2118_;
}
v___jp_2119_:
{
if (lean_obj_tag(v___y_2120_) == 0)
{
lean_object* v_a_2121_; 
v_a_2121_ = lean_ctor_get(v___y_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v___y_2120_, 1);
v_a_2112_ = v_a_2121_;
goto v___jp_2111_;
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_b_2105_);
lean_dec_ref(v_xs_2104_);
v_a_2122_ = lean_ctor_get(v___y_2120_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___y_2120_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___y_2120_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___y_2120_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object* v_a_2140_, lean_object* v_lctx_2141_, lean_object* v_xs_2142_, lean_object* v_b_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v_a_11032__boxed_2149_; lean_object* v_res_2150_; 
v_a_11032__boxed_2149_ = lean_unbox(v_a_2140_);
v_res_2150_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_11032__boxed_2149_, v_lctx_2141_, v_xs_2142_, v_b_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object* v_e_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; 
lean_inc_ref(v_e_2151_);
v___x_2157_ = l_Lean_Meta_isProof(v_e_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2195_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2195_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2195_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_unbox(v_a_2158_);
if (v___x_2162_ == 0)
{
uint8_t v___x_2163_; 
v___x_2163_ = l_Lean_Expr_isLet(v_e_2151_);
if (v___x_2163_ == 0)
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_dec(v_a_2158_);
lean_dec_ref(v_e_2151_);
v___x_2164_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2164_);
v___x_2166_ = v___x_2160_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
else
{
lean_object* v_lctx_2168_; lean_object* v___f_2169_; uint8_t v___x_2170_; uint8_t v___x_2171_; lean_object* v___x_2172_; 
lean_del_object(v___x_2160_);
v_lctx_2168_ = lean_ctor_get(v___y_2152_, 2);
lean_inc_ref(v_lctx_2168_);
lean_inc(v_a_2158_);
v___f_2169_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2169_, 0, v_a_2158_);
lean_closure_set(v___f_2169_, 1, v_lctx_2168_);
v___x_2170_ = lean_unbox(v_a_2158_);
v___x_2171_ = lean_unbox(v_a_2158_);
lean_dec(v_a_2158_);
v___x_2172_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2151_, v___f_2169_, v___x_2170_, v___x_2163_, v___x_2171_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2182_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2175_ = v___x_2172_;
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2172_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2182_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2177_, 0, v_a_2173_);
v___x_2178_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set(v___x_2175_, 0, v___x_2178_);
v___x_2180_ = v___x_2175_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
v_a_2183_ = lean_ctor_get(v___x_2172_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2172_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2172_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2172_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2193_; 
lean_dec(v_a_2158_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_e_2151_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2191_);
v___x_2193_ = v___x_2160_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
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
else
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2203_; 
lean_dec_ref(v_e_2151_);
v_a_2196_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2198_ = v___x_2157_;
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2157_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2203_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2201_; 
if (v_isShared_2199_ == 0)
{
v___x_2201_ = v___x_2198_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_a_2196_);
v___x_2201_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
return v___x_2201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object* v_e_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object* v_00_u03b1_2211_, lean_object* v_x_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_apply_1(v_x_2212_, lean_box(0));
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
return v___x_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2220_, lean_object* v_x_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(v_00_u03b1_2220_, v_x_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
return v_res_2227_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = l_Lean_maxRecDepthErrorMessage;
v___x_2234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3);
v___x_2236_ = l_Lean_MessageData_ofFormat(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4);
v___x_2238_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2));
v___x_2239_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v___x_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object* v_ref_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v_ref_2240_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
v___x_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object* v_ref_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2245_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___y_2256_; lean_object* v_fileName_2265_; lean_object* v_fileMap_2266_; lean_object* v_options_2267_; lean_object* v_currRecDepth_2268_; lean_object* v_maxRecDepth_2269_; lean_object* v_ref_2270_; lean_object* v_currNamespace_2271_; lean_object* v_openDecls_2272_; lean_object* v_initHeartbeats_2273_; lean_object* v_maxHeartbeats_2274_; lean_object* v_quotContext_2275_; lean_object* v_currMacroScope_2276_; uint8_t v_diag_2277_; lean_object* v_cancelTk_x3f_2278_; uint8_t v_suppressElabErrors_2279_; lean_object* v_inheritedTraceOptions_2280_; uint8_t v___y_2282_; lean_object* v___x_2288_; uint8_t v___x_2289_; uint8_t v___x_2290_; 
v_fileName_2265_ = lean_ctor_get(v___y_2252_, 0);
v_fileMap_2266_ = lean_ctor_get(v___y_2252_, 1);
v_options_2267_ = lean_ctor_get(v___y_2252_, 2);
v_currRecDepth_2268_ = lean_ctor_get(v___y_2252_, 3);
v_maxRecDepth_2269_ = lean_ctor_get(v___y_2252_, 4);
v_ref_2270_ = lean_ctor_get(v___y_2252_, 5);
v_currNamespace_2271_ = lean_ctor_get(v___y_2252_, 6);
v_openDecls_2272_ = lean_ctor_get(v___y_2252_, 7);
v_initHeartbeats_2273_ = lean_ctor_get(v___y_2252_, 8);
v_maxHeartbeats_2274_ = lean_ctor_get(v___y_2252_, 9);
v_quotContext_2275_ = lean_ctor_get(v___y_2252_, 10);
v_currMacroScope_2276_ = lean_ctor_get(v___y_2252_, 11);
v_diag_2277_ = lean_ctor_get_uint8(v___y_2252_, sizeof(void*)*14);
v_cancelTk_x3f_2278_ = lean_ctor_get(v___y_2252_, 12);
v_suppressElabErrors_2279_ = lean_ctor_get_uint8(v___y_2252_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2280_ = lean_ctor_get(v___y_2252_, 13);
v___x_2288_ = lean_unsigned_to_nat(0u);
v___x_2289_ = lean_nat_dec_eq(v_maxRecDepth_2269_, v___x_2288_);
v___x_2290_ = lean_bool_not(v___x_2289_);
if (v___x_2290_ == 0)
{
v___y_2282_ = v___x_2290_;
goto v___jp_2281_;
}
else
{
uint8_t v___x_2291_; 
v___x_2291_ = lean_nat_dec_eq(v_currRecDepth_2268_, v_maxRecDepth_2269_);
v___y_2282_ = v___x_2291_;
goto v___jp_2281_;
}
v___jp_2255_:
{
if (lean_obj_tag(v___y_2256_) == 0)
{
return v___y_2256_;
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
v_a_2257_ = lean_ctor_get(v___y_2256_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___y_2256_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___y_2256_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___y_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
v___jp_2281_:
{
if (v___y_2282_ == 0)
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2283_ = lean_unsigned_to_nat(1u);
v___x_2284_ = lean_nat_add(v_currRecDepth_2268_, v___x_2283_);
lean_inc_ref(v_inheritedTraceOptions_2280_);
lean_inc(v_cancelTk_x3f_2278_);
lean_inc(v_currMacroScope_2276_);
lean_inc(v_quotContext_2275_);
lean_inc(v_maxHeartbeats_2274_);
lean_inc(v_initHeartbeats_2273_);
lean_inc(v_openDecls_2272_);
lean_inc(v_currNamespace_2271_);
lean_inc(v_ref_2270_);
lean_inc(v_maxRecDepth_2269_);
lean_inc_ref(v_options_2267_);
lean_inc_ref(v_fileMap_2266_);
lean_inc_ref(v_fileName_2265_);
v___x_2285_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2285_, 0, v_fileName_2265_);
lean_ctor_set(v___x_2285_, 1, v_fileMap_2266_);
lean_ctor_set(v___x_2285_, 2, v_options_2267_);
lean_ctor_set(v___x_2285_, 3, v___x_2284_);
lean_ctor_set(v___x_2285_, 4, v_maxRecDepth_2269_);
lean_ctor_set(v___x_2285_, 5, v_ref_2270_);
lean_ctor_set(v___x_2285_, 6, v_currNamespace_2271_);
lean_ctor_set(v___x_2285_, 7, v_openDecls_2272_);
lean_ctor_set(v___x_2285_, 8, v_initHeartbeats_2273_);
lean_ctor_set(v___x_2285_, 9, v_maxHeartbeats_2274_);
lean_ctor_set(v___x_2285_, 10, v_quotContext_2275_);
lean_ctor_set(v___x_2285_, 11, v_currMacroScope_2276_);
lean_ctor_set(v___x_2285_, 12, v_cancelTk_x3f_2278_);
lean_ctor_set(v___x_2285_, 13, v_inheritedTraceOptions_2280_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*14, v_diag_2277_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*14 + 1, v_suppressElabErrors_2279_);
lean_inc(v___y_2253_);
lean_inc(v___y_2251_);
lean_inc_ref(v___y_2250_);
lean_inc(v___y_2249_);
v___x_2286_ = lean_apply_6(v_x_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___x_2285_, v___y_2253_, lean_box(0));
v___y_2256_ = v___x_2286_;
goto v___jp_2255_;
}
else
{
lean_object* v___x_2287_; 
lean_dec_ref(v_x_2248_);
lean_inc(v_ref_2270_);
v___x_2287_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2270_);
v___y_2256_ = v___x_2287_;
goto v___jp_2255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object* v_a_2300_, lean_object* v_x_2301_){
_start:
{
if (lean_obj_tag(v_x_2301_) == 0)
{
lean_object* v___x_2302_; 
v___x_2302_ = lean_box(0);
return v___x_2302_;
}
else
{
lean_object* v_key_2303_; lean_object* v_value_2304_; lean_object* v_tail_2305_; uint8_t v___x_2306_; 
v_key_2303_ = lean_ctor_get(v_x_2301_, 0);
v_value_2304_ = lean_ctor_get(v_x_2301_, 1);
v_tail_2305_ = lean_ctor_get(v_x_2301_, 2);
v___x_2306_ = l_Lean_ExprStructEq_beq(v_key_2303_, v_a_2300_);
if (v___x_2306_ == 0)
{
v_x_2301_ = v_tail_2305_;
goto _start;
}
else
{
lean_object* v___x_2308_; 
lean_inc(v_value_2304_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v_value_2304_);
return v___x_2308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_a_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2309_, v_x_2310_);
lean_dec(v_x_2310_);
lean_dec_ref(v_a_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_m_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v_buckets_2314_; lean_object* v___x_2315_; uint64_t v___x_2316_; uint64_t v___x_2317_; uint64_t v___x_2318_; uint64_t v_fold_2319_; uint64_t v___x_2320_; uint64_t v___x_2321_; uint64_t v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; size_t v___x_2325_; size_t v___x_2326_; size_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_buckets_2314_ = lean_ctor_get(v_m_2312_, 1);
v___x_2315_ = lean_array_get_size(v_buckets_2314_);
v___x_2316_ = l_Lean_ExprStructEq_hash(v_a_2313_);
v___x_2317_ = 32ULL;
v___x_2318_ = lean_uint64_shift_right(v___x_2316_, v___x_2317_);
v_fold_2319_ = lean_uint64_xor(v___x_2316_, v___x_2318_);
v___x_2320_ = 16ULL;
v___x_2321_ = lean_uint64_shift_right(v_fold_2319_, v___x_2320_);
v___x_2322_ = lean_uint64_xor(v_fold_2319_, v___x_2321_);
v___x_2323_ = lean_uint64_to_usize(v___x_2322_);
v___x_2324_ = lean_usize_of_nat(v___x_2315_);
v___x_2325_ = ((size_t)1ULL);
v___x_2326_ = lean_usize_sub(v___x_2324_, v___x_2325_);
v___x_2327_ = lean_usize_land(v___x_2323_, v___x_2326_);
v___x_2328_ = lean_array_uget_borrowed(v_buckets_2314_, v___x_2327_);
v___x_2329_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2313_, v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_m_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_2330_, v_a_2331_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_m_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2333_, lean_object* v___y_2334_, lean_object* v_b_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
lean_inc(v___y_2339_);
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___y_2334_);
v___x_2341_ = lean_apply_7(v_k_2333_, v_b_2335_, v___y_2334_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, lean_box(0));
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2342_, lean_object* v___y_2343_, lean_object* v_b_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2342_, v___y_2343_, v_b_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2343_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2351_, uint8_t v_bi_2352_, lean_object* v_type_2353_, lean_object* v_k_2354_, uint8_t v_kind_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v___f_2362_; lean_object* v___x_2363_; 
lean_inc(v___y_2356_);
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2362_, 0, v_k_2354_);
lean_closure_set(v___f_2362_, 1, v___y_2356_);
v___x_2363_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2351_, v_bi_2352_, v_type_2353_, v___f_2362_, v_kind_2355_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
if (lean_obj_tag(v___x_2363_) == 0)
{
return v___x_2363_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2372_, lean_object* v_bi_2373_, lean_object* v_type_2374_, lean_object* v_k_2375_, lean_object* v_kind_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
uint8_t v_bi_boxed_2383_; uint8_t v_kind_boxed_2384_; lean_object* v_res_2385_; 
v_bi_boxed_2383_ = lean_unbox(v_bi_2373_);
v_kind_boxed_2384_ = lean_unbox(v_kind_2376_);
v_res_2385_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2372_, v_bi_boxed_2383_, v_type_2374_, v_k_2375_, v_kind_boxed_2384_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object* v___x_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2386_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2400_, lean_object* v_type_2401_, lean_object* v_val_2402_, lean_object* v_k_2403_, uint8_t v_nondep_2404_, uint8_t v_kind_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___f_2412_; lean_object* v___x_2413_; 
lean_inc(v___y_2406_);
v___f_2412_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2412_, 0, v_k_2403_);
lean_closure_set(v___f_2412_, 1, v___y_2406_);
v___x_2413_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2400_, v_type_2401_, v_val_2402_, v___f_2412_, v_nondep_2404_, v_kind_2405_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2413_) == 0)
{
return v___x_2413_;
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2413_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2413_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2422_, lean_object* v_type_2423_, lean_object* v_val_2424_, lean_object* v_k_2425_, lean_object* v_nondep_2426_, lean_object* v_kind_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
uint8_t v_nondep_boxed_2434_; uint8_t v_kind_boxed_2435_; lean_object* v_res_2436_; 
v_nondep_boxed_2434_ = lean_unbox(v_nondep_2426_);
v_kind_boxed_2435_ = lean_unbox(v_kind_2427_);
v_res_2436_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2422_, v_type_2423_, v_val_2424_, v_k_2425_, v_nondep_boxed_2434_, v_kind_boxed_2435_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2437_, lean_object* v_x_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_apply_1(v_x_2438_, lean_box(0));
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2446_, lean_object* v_x_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2446_, v_x_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
return v_res_2453_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2454_, lean_object* v_x_2455_){
_start:
{
if (lean_obj_tag(v_x_2455_) == 0)
{
uint8_t v___x_2456_; 
v___x_2456_ = 0;
return v___x_2456_;
}
else
{
lean_object* v_key_2457_; lean_object* v_tail_2458_; uint8_t v___x_2459_; 
v_key_2457_ = lean_ctor_get(v_x_2455_, 0);
v_tail_2458_ = lean_ctor_get(v_x_2455_, 2);
v___x_2459_ = l_Lean_ExprStructEq_beq(v_key_2457_, v_a_2454_);
if (v___x_2459_ == 0)
{
v_x_2455_ = v_tail_2458_;
goto _start;
}
else
{
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2461_, lean_object* v_x_2462_){
_start:
{
uint8_t v_res_2463_; lean_object* v_r_2464_; 
v_res_2463_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2461_, v_x_2462_);
lean_dec(v_x_2462_);
lean_dec_ref(v_a_2461_);
v_r_2464_ = lean_box(v_res_2463_);
return v_r_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2465_, lean_object* v_b_2466_, lean_object* v_x_2467_){
_start:
{
if (lean_obj_tag(v_x_2467_) == 0)
{
lean_dec(v_b_2466_);
lean_dec_ref(v_a_2465_);
return v_x_2467_;
}
else
{
lean_object* v_key_2468_; lean_object* v_value_2469_; lean_object* v_tail_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2482_; 
v_key_2468_ = lean_ctor_get(v_x_2467_, 0);
v_value_2469_ = lean_ctor_get(v_x_2467_, 1);
v_tail_2470_ = lean_ctor_get(v_x_2467_, 2);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_x_2467_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2472_ = v_x_2467_;
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_tail_2470_);
lean_inc(v_value_2469_);
lean_inc(v_key_2468_);
lean_dec(v_x_2467_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2482_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
uint8_t v___x_2474_; 
v___x_2474_ = l_Lean_ExprStructEq_beq(v_key_2468_, v_a_2465_);
if (v___x_2474_ == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2465_, v_b_2466_, v_tail_2470_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 2, v___x_2475_);
v___x_2477_ = v___x_2472_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_key_2468_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_value_2469_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
else
{
lean_object* v___x_2480_; 
lean_dec(v_value_2469_);
lean_dec(v_key_2468_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 1, v_b_2466_);
lean_ctor_set(v___x_2472_, 0, v_a_2465_);
v___x_2480_ = v___x_2472_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2465_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v_b_2466_);
lean_ctor_set(v_reuseFailAlloc_2481_, 2, v_tail_2470_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2483_, lean_object* v_x_2484_){
_start:
{
if (lean_obj_tag(v_x_2484_) == 0)
{
return v_x_2483_;
}
else
{
lean_object* v_key_2485_; lean_object* v_value_2486_; lean_object* v_tail_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2510_; 
v_key_2485_ = lean_ctor_get(v_x_2484_, 0);
v_value_2486_ = lean_ctor_get(v_x_2484_, 1);
v_tail_2487_ = lean_ctor_get(v_x_2484_, 2);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_x_2484_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2489_ = v_x_2484_;
v_isShared_2490_ = v_isSharedCheck_2510_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_tail_2487_);
lean_inc(v_value_2486_);
lean_inc(v_key_2485_);
lean_dec(v_x_2484_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2510_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; uint64_t v___x_2494_; uint64_t v_fold_2495_; uint64_t v___x_2496_; uint64_t v___x_2497_; uint64_t v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; size_t v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2491_ = lean_array_get_size(v_x_2483_);
v___x_2492_ = l_Lean_ExprStructEq_hash(v_key_2485_);
v___x_2493_ = 32ULL;
v___x_2494_ = lean_uint64_shift_right(v___x_2492_, v___x_2493_);
v_fold_2495_ = lean_uint64_xor(v___x_2492_, v___x_2494_);
v___x_2496_ = 16ULL;
v___x_2497_ = lean_uint64_shift_right(v_fold_2495_, v___x_2496_);
v___x_2498_ = lean_uint64_xor(v_fold_2495_, v___x_2497_);
v___x_2499_ = lean_uint64_to_usize(v___x_2498_);
v___x_2500_ = lean_usize_of_nat(v___x_2491_);
v___x_2501_ = ((size_t)1ULL);
v___x_2502_ = lean_usize_sub(v___x_2500_, v___x_2501_);
v___x_2503_ = lean_usize_land(v___x_2499_, v___x_2502_);
v___x_2504_ = lean_array_uget_borrowed(v_x_2483_, v___x_2503_);
lean_inc(v___x_2504_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 2, v___x_2504_);
v___x_2506_ = v___x_2489_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_key_2485_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_value_2486_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
lean_object* v___x_2507_; 
v___x_2507_ = lean_array_uset(v_x_2483_, v___x_2503_, v___x_2506_);
v_x_2483_ = v___x_2507_;
v_x_2484_ = v_tail_2487_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2511_, lean_object* v_source_2512_, lean_object* v_target_2513_){
_start:
{
lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2514_ = lean_array_get_size(v_source_2512_);
v___x_2515_ = lean_nat_dec_lt(v_i_2511_, v___x_2514_);
if (v___x_2515_ == 0)
{
lean_dec_ref(v_source_2512_);
lean_dec(v_i_2511_);
return v_target_2513_;
}
else
{
lean_object* v_es_2516_; lean_object* v___x_2517_; lean_object* v_source_2518_; lean_object* v_target_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_es_2516_ = lean_array_fget(v_source_2512_, v_i_2511_);
v___x_2517_ = lean_box(0);
v_source_2518_ = lean_array_fset(v_source_2512_, v_i_2511_, v___x_2517_);
v_target_2519_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2513_, v_es_2516_);
v___x_2520_ = lean_unsigned_to_nat(1u);
v___x_2521_ = lean_nat_add(v_i_2511_, v___x_2520_);
lean_dec(v_i_2511_);
v_i_2511_ = v___x_2521_;
v_source_2512_ = v_source_2518_;
v_target_2513_ = v_target_2519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2523_){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v_nbuckets_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2524_ = lean_array_get_size(v_data_2523_);
v___x_2525_ = lean_unsigned_to_nat(2u);
v_nbuckets_2526_ = lean_nat_mul(v___x_2524_, v___x_2525_);
v___x_2527_ = lean_unsigned_to_nat(0u);
v___x_2528_ = lean_box(0);
v___x_2529_ = lean_mk_array(v_nbuckets_2526_, v___x_2528_);
v___x_2530_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2527_, v_data_2523_, v___x_2529_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2531_, lean_object* v_a_2532_, lean_object* v_b_2533_){
_start:
{
lean_object* v_size_2534_; lean_object* v_buckets_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2578_; 
v_size_2534_ = lean_ctor_get(v_m_2531_, 0);
v_buckets_2535_ = lean_ctor_get(v_m_2531_, 1);
v_isSharedCheck_2578_ = !lean_is_exclusive(v_m_2531_);
if (v_isSharedCheck_2578_ == 0)
{
v___x_2537_ = v_m_2531_;
v_isShared_2538_ = v_isSharedCheck_2578_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_buckets_2535_);
lean_inc(v_size_2534_);
lean_dec(v_m_2531_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2578_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; uint64_t v___x_2540_; uint64_t v___x_2541_; uint64_t v___x_2542_; uint64_t v_fold_2543_; uint64_t v___x_2544_; uint64_t v___x_2545_; uint64_t v___x_2546_; size_t v___x_2547_; size_t v___x_2548_; size_t v___x_2549_; size_t v___x_2550_; size_t v___x_2551_; lean_object* v_bkt_2552_; uint8_t v___x_2553_; 
v___x_2539_ = lean_array_get_size(v_buckets_2535_);
v___x_2540_ = l_Lean_ExprStructEq_hash(v_a_2532_);
v___x_2541_ = 32ULL;
v___x_2542_ = lean_uint64_shift_right(v___x_2540_, v___x_2541_);
v_fold_2543_ = lean_uint64_xor(v___x_2540_, v___x_2542_);
v___x_2544_ = 16ULL;
v___x_2545_ = lean_uint64_shift_right(v_fold_2543_, v___x_2544_);
v___x_2546_ = lean_uint64_xor(v_fold_2543_, v___x_2545_);
v___x_2547_ = lean_uint64_to_usize(v___x_2546_);
v___x_2548_ = lean_usize_of_nat(v___x_2539_);
v___x_2549_ = ((size_t)1ULL);
v___x_2550_ = lean_usize_sub(v___x_2548_, v___x_2549_);
v___x_2551_ = lean_usize_land(v___x_2547_, v___x_2550_);
v_bkt_2552_ = lean_array_uget_borrowed(v_buckets_2535_, v___x_2551_);
v___x_2553_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2532_, v_bkt_2552_);
if (v___x_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v_size_x27_2555_; lean_object* v___x_2556_; lean_object* v_buckets_x27_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; uint8_t v___x_2563_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v_size_x27_2555_ = lean_nat_add(v_size_2534_, v___x_2554_);
lean_dec(v_size_2534_);
lean_inc(v_bkt_2552_);
v___x_2556_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2556_, 0, v_a_2532_);
lean_ctor_set(v___x_2556_, 1, v_b_2533_);
lean_ctor_set(v___x_2556_, 2, v_bkt_2552_);
v_buckets_x27_2557_ = lean_array_uset(v_buckets_2535_, v___x_2551_, v___x_2556_);
v___x_2558_ = lean_unsigned_to_nat(4u);
v___x_2559_ = lean_nat_mul(v_size_x27_2555_, v___x_2558_);
v___x_2560_ = lean_unsigned_to_nat(3u);
v___x_2561_ = lean_nat_div(v___x_2559_, v___x_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_array_get_size(v_buckets_x27_2557_);
v___x_2563_ = lean_nat_dec_le(v___x_2561_, v___x_2562_);
lean_dec(v___x_2561_);
if (v___x_2563_ == 0)
{
lean_object* v_val_2564_; lean_object* v___x_2566_; 
v_val_2564_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2557_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v_val_2564_);
lean_ctor_set(v___x_2537_, 0, v_size_x27_2555_);
v___x_2566_ = v___x_2537_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_size_x27_2555_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_val_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
else
{
lean_object* v___x_2569_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v_buckets_x27_2557_);
lean_ctor_set(v___x_2537_, 0, v_size_x27_2555_);
v___x_2569_ = v___x_2537_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_size_x27_2555_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_buckets_x27_2557_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
else
{
lean_object* v___x_2571_; lean_object* v_buckets_x27_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
lean_inc(v_bkt_2552_);
v___x_2571_ = lean_box(0);
v_buckets_x27_2572_ = lean_array_uset(v_buckets_2535_, v___x_2551_, v___x_2571_);
v___x_2573_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2532_, v_b_2533_, v_bkt_2552_);
v___x_2574_ = lean_array_uset(v_buckets_x27_2572_, v___x_2551_, v___x_2573_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v___x_2574_);
v___x_2576_ = v___x_2537_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_size_2534_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2574_);
v___x_2576_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
return v___x_2576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2579_, lean_object* v_e_2580_, lean_object* v_a_2581_){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2583_ = lean_st_ref_take(v_a_2579_);
v___x_2584_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2583_, v_e_2580_, v_a_2581_);
v___x_2585_ = lean_st_ref_set(v_a_2579_, v___x_2584_);
v___x_2586_ = lean_box(0);
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2587_, lean_object* v_e_2588_, lean_object* v_a_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v_res_2591_; 
v_res_2591_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2587_, v_e_2588_, v_a_2589_);
lean_dec(v_a_2587_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2595_, lean_object* v_pre_2596_, lean_object* v_post_2597_, uint8_t v_usedLetOnly_2598_, uint8_t v_skipConstInApp_2599_, uint8_t v_skipInstances_2600_, lean_object* v_body_2601_, lean_object* v_x_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = lean_array_push(v_fvars_2595_, v_x_2602_);
v___x_2610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2596_, v_post_2597_, v_usedLetOnly_2598_, v_skipConstInApp_2599_, v_skipInstances_2600_, v___x_2609_, v_body_2601_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2611_, lean_object* v_pre_2612_, lean_object* v_post_2613_, lean_object* v_usedLetOnly_2614_, lean_object* v_skipConstInApp_2615_, lean_object* v_skipInstances_2616_, lean_object* v_body_2617_, lean_object* v_x_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
uint8_t v_usedLetOnly_boxed_2625_; uint8_t v_skipConstInApp_boxed_2626_; uint8_t v_skipInstances_boxed_2627_; lean_object* v_res_2628_; 
v_usedLetOnly_boxed_2625_ = lean_unbox(v_usedLetOnly_2614_);
v_skipConstInApp_boxed_2626_ = lean_unbox(v_skipConstInApp_2615_);
v_skipInstances_boxed_2627_ = lean_unbox(v_skipInstances_2616_);
v_res_2628_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2611_, v_pre_2612_, v_post_2613_, v_usedLetOnly_boxed_2625_, v_skipConstInApp_boxed_2626_, v_skipInstances_boxed_2627_, v_body_2617_, v_x_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2629_, lean_object* v_post_2630_, uint8_t v_usedLetOnly_2631_, uint8_t v_skipConstInApp_2632_, uint8_t v_skipInstances_2633_, lean_object* v_e_2634_, lean_object* v_a_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
lean_inc_ref(v_post_2630_);
lean_inc(v___y_2639_);
lean_inc_ref(v___y_2638_);
lean_inc(v___y_2637_);
lean_inc_ref(v___y_2636_);
lean_inc_ref(v_e_2634_);
v___x_2641_ = lean_apply_6(v_post_2630_, v_e_2634_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, lean_box(0));
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2660_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2644_ = v___x_2641_;
v_isShared_2645_ = v_isSharedCheck_2660_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2641_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2660_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
switch(lean_obj_tag(v_a_2642_))
{
case 0:
{
lean_object* v_e_2646_; lean_object* v___x_2648_; 
lean_dec_ref(v_e_2634_);
lean_dec_ref(v_post_2630_);
lean_dec_ref(v_pre_2629_);
v_e_2646_ = lean_ctor_get(v_a_2642_, 0);
lean_inc_ref(v_e_2646_);
lean_dec_ref_known(v_a_2642_, 1);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_e_2646_);
v___x_2648_ = v___x_2644_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_e_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
case 1:
{
lean_object* v_e_2650_; lean_object* v___x_2651_; 
lean_del_object(v___x_2644_);
lean_dec_ref(v_e_2634_);
v_e_2650_ = lean_ctor_get(v_a_2642_, 0);
lean_inc_ref(v_e_2650_);
lean_dec_ref_known(v_a_2642_, 1);
v___x_2651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2629_, v_post_2630_, v_usedLetOnly_2631_, v_skipConstInApp_2632_, v_skipInstances_2633_, v_e_2650_, v_a_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2651_;
}
default: 
{
lean_object* v_e_x3f_2652_; 
lean_dec_ref(v_post_2630_);
lean_dec_ref(v_pre_2629_);
v_e_x3f_2652_ = lean_ctor_get(v_a_2642_, 0);
lean_inc(v_e_x3f_2652_);
lean_dec_ref_known(v_a_2642_, 1);
if (lean_obj_tag(v_e_x3f_2652_) == 0)
{
lean_object* v___x_2654_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_e_2634_);
v___x_2654_ = v___x_2644_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_e_2634_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
else
{
lean_object* v_val_2656_; lean_object* v___x_2658_; 
lean_dec_ref(v_e_2634_);
v_val_2656_ = lean_ctor_get(v_e_x3f_2652_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v_e_x3f_2652_, 1);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v_val_2656_);
v___x_2658_ = v___x_2644_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_val_2656_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_dec_ref(v_e_2634_);
lean_dec_ref(v_post_2630_);
lean_dec_ref(v_pre_2629_);
v_a_2661_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2641_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2641_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2669_, lean_object* v_post_2670_, uint8_t v_usedLetOnly_2671_, uint8_t v_skipConstInApp_2672_, uint8_t v_skipInstances_2673_, lean_object* v_fvars_2674_, lean_object* v_e_2675_, lean_object* v_a_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
if (lean_obj_tag(v_e_2675_) == 6)
{
lean_object* v_binderName_2682_; lean_object* v_binderType_2683_; lean_object* v_body_2684_; uint8_t v_binderInfo_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v_binderName_2682_ = lean_ctor_get(v_e_2675_, 0);
lean_inc(v_binderName_2682_);
v_binderType_2683_ = lean_ctor_get(v_e_2675_, 1);
lean_inc_ref(v_binderType_2683_);
v_body_2684_ = lean_ctor_get(v_e_2675_, 2);
lean_inc_ref(v_body_2684_);
v_binderInfo_2685_ = lean_ctor_get_uint8(v_e_2675_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2675_, 3);
v___x_2686_ = lean_expr_instantiate_rev(v_binderType_2683_, v_fvars_2674_);
lean_dec_ref(v_binderType_2683_);
lean_inc_ref(v_post_2670_);
lean_inc_ref(v_pre_2669_);
v___x_2687_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2669_, v_post_2670_, v_usedLetOnly_2671_, v_skipConstInApp_2672_, v_skipInstances_2673_, v___x_2686_, v_a_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref_known(v___x_2687_, 1);
v___x_2689_ = lean_box(v_usedLetOnly_2671_);
v___x_2690_ = lean_box(v_skipConstInApp_2672_);
v___x_2691_ = lean_box(v_skipInstances_2673_);
v___f_2692_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2692_, 0, v_fvars_2674_);
lean_closure_set(v___f_2692_, 1, v_pre_2669_);
lean_closure_set(v___f_2692_, 2, v_post_2670_);
lean_closure_set(v___f_2692_, 3, v___x_2689_);
lean_closure_set(v___f_2692_, 4, v___x_2690_);
lean_closure_set(v___f_2692_, 5, v___x_2691_);
lean_closure_set(v___f_2692_, 6, v_body_2684_);
v___x_2693_ = 0;
v___x_2694_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2682_, v_binderInfo_2685_, v_a_2688_, v___f_2692_, v___x_2693_, v_a_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
return v___x_2694_;
}
else
{
lean_dec_ref(v_body_2684_);
lean_dec(v_binderName_2682_);
lean_dec_ref(v_fvars_2674_);
lean_dec_ref(v_post_2670_);
lean_dec_ref(v_pre_2669_);
return v___x_2687_;
}
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = lean_expr_instantiate_rev(v_e_2675_, v_fvars_2674_);
lean_dec_ref(v_e_2675_);
lean_inc_ref(v_post_2670_);
lean_inc_ref(v_pre_2669_);
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2669_, v_post_2670_, v_usedLetOnly_2671_, v_skipConstInApp_2672_, v_skipInstances_2673_, v___x_2695_, v_a_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; uint8_t v___x_2698_; uint8_t v___x_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2696_, 1);
v___x_2698_ = 0;
v___x_2699_ = 1;
v___x_2700_ = 1;
v___x_2701_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2674_, v_a_2697_, v___x_2698_, v_usedLetOnly_2671_, v___x_2698_, v___x_2699_, v___x_2700_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
lean_dec_ref(v_fvars_2674_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2669_, v_post_2670_, v_usedLetOnly_2671_, v_skipConstInApp_2672_, v_skipInstances_2673_, v_a_2702_, v_a_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
return v___x_2703_;
}
else
{
lean_dec_ref(v_post_2670_);
lean_dec_ref(v_pre_2669_);
return v___x_2701_;
}
}
else
{
lean_dec_ref(v_fvars_2674_);
lean_dec_ref(v_post_2670_);
lean_dec_ref(v_pre_2669_);
return v___x_2696_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2704_, lean_object* v_pre_2705_, lean_object* v_post_2706_, uint8_t v_usedLetOnly_2707_, uint8_t v_skipConstInApp_2708_, uint8_t v_skipInstances_2709_, lean_object* v_body_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = lean_array_push(v_fvars_2704_, v_x_2711_);
v___x_2719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2705_, v_post_2706_, v_usedLetOnly_2707_, v_skipConstInApp_2708_, v_skipInstances_2709_, v___x_2718_, v_body_2710_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2720_, lean_object* v_pre_2721_, lean_object* v_post_2722_, lean_object* v_usedLetOnly_2723_, lean_object* v_skipConstInApp_2724_, lean_object* v_skipInstances_2725_, lean_object* v_body_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
uint8_t v_usedLetOnly_boxed_2734_; uint8_t v_skipConstInApp_boxed_2735_; uint8_t v_skipInstances_boxed_2736_; lean_object* v_res_2737_; 
v_usedLetOnly_boxed_2734_ = lean_unbox(v_usedLetOnly_2723_);
v_skipConstInApp_boxed_2735_ = lean_unbox(v_skipConstInApp_2724_);
v_skipInstances_boxed_2736_ = lean_unbox(v_skipInstances_2725_);
v_res_2737_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2720_, v_pre_2721_, v_post_2722_, v_usedLetOnly_boxed_2734_, v_skipConstInApp_boxed_2735_, v_skipInstances_boxed_2736_, v_body_2726_, v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2738_, lean_object* v_post_2739_, uint8_t v_usedLetOnly_2740_, uint8_t v_skipConstInApp_2741_, uint8_t v_skipInstances_2742_, lean_object* v_fvars_2743_, lean_object* v_e_2744_, lean_object* v_a_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
if (lean_obj_tag(v_e_2744_) == 8)
{
lean_object* v_declName_2751_; lean_object* v_type_2752_; lean_object* v_value_2753_; lean_object* v_body_2754_; uint8_t v_nondep_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v_declName_2751_ = lean_ctor_get(v_e_2744_, 0);
lean_inc(v_declName_2751_);
v_type_2752_ = lean_ctor_get(v_e_2744_, 1);
lean_inc_ref(v_type_2752_);
v_value_2753_ = lean_ctor_get(v_e_2744_, 2);
lean_inc_ref(v_value_2753_);
v_body_2754_ = lean_ctor_get(v_e_2744_, 3);
lean_inc_ref(v_body_2754_);
v_nondep_2755_ = lean_ctor_get_uint8(v_e_2744_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2744_, 4);
v___x_2756_ = lean_expr_instantiate_rev(v_type_2752_, v_fvars_2743_);
lean_dec_ref(v_type_2752_);
lean_inc_ref(v_post_2739_);
lean_inc_ref(v_pre_2738_);
v___x_2757_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2738_, v_post_2739_, v_usedLetOnly_2740_, v_skipConstInApp_2741_, v_skipInstances_2742_, v___x_2756_, v_a_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2757_) == 0)
{
lean_object* v_a_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; 
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
lean_inc(v_a_2758_);
lean_dec_ref_known(v___x_2757_, 1);
v___x_2759_ = lean_expr_instantiate_rev(v_value_2753_, v_fvars_2743_);
lean_dec_ref(v_value_2753_);
lean_inc_ref(v_post_2739_);
lean_inc_ref(v_pre_2738_);
v___x_2760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2738_, v_post_2739_, v_usedLetOnly_2740_, v_skipConstInApp_2741_, v_skipInstances_2742_, v___x_2759_, v_a_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___f_2765_; uint8_t v___x_2766_; lean_object* v___x_2767_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v___x_2762_ = lean_box(v_usedLetOnly_2740_);
v___x_2763_ = lean_box(v_skipConstInApp_2741_);
v___x_2764_ = lean_box(v_skipInstances_2742_);
v___f_2765_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2765_, 0, v_fvars_2743_);
lean_closure_set(v___f_2765_, 1, v_pre_2738_);
lean_closure_set(v___f_2765_, 2, v_post_2739_);
lean_closure_set(v___f_2765_, 3, v___x_2762_);
lean_closure_set(v___f_2765_, 4, v___x_2763_);
lean_closure_set(v___f_2765_, 5, v___x_2764_);
lean_closure_set(v___f_2765_, 6, v_body_2754_);
v___x_2766_ = 0;
v___x_2767_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2751_, v_a_2758_, v_a_2761_, v___f_2765_, v_nondep_2755_, v___x_2766_, v_a_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2767_;
}
else
{
lean_dec(v_a_2758_);
lean_dec_ref(v_body_2754_);
lean_dec(v_declName_2751_);
lean_dec_ref(v_fvars_2743_);
lean_dec_ref(v_post_2739_);
lean_dec_ref(v_pre_2738_);
return v___x_2760_;
}
}
else
{
lean_dec_ref(v_body_2754_);
lean_dec_ref(v_value_2753_);
lean_dec(v_declName_2751_);
lean_dec_ref(v_fvars_2743_);
lean_dec_ref(v_post_2739_);
lean_dec_ref(v_pre_2738_);
return v___x_2757_;
}
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_expr_instantiate_rev(v_e_2744_, v_fvars_2743_);
lean_dec_ref(v_e_2744_);
lean_inc_ref(v_post_2739_);
lean_inc_ref(v_pre_2738_);
v___x_2769_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2738_, v_post_2739_, v_usedLetOnly_2740_, v_skipConstInApp_2741_, v_skipInstances_2742_, v___x_2768_, v_a_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; uint8_t v___x_2771_; uint8_t v___x_2772_; lean_object* v___x_2773_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = 0;
v___x_2772_ = 1;
v___x_2773_ = l_Lean_Meta_mkLetFVars(v_fvars_2743_, v_a_2770_, v_usedLetOnly_2740_, v___x_2771_, v___x_2772_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec_ref(v_fvars_2743_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2738_, v_post_2739_, v_usedLetOnly_2740_, v_skipConstInApp_2741_, v_skipInstances_2742_, v_a_2774_, v_a_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2775_;
}
else
{
lean_dec_ref(v_post_2739_);
lean_dec_ref(v_pre_2738_);
return v___x_2773_;
}
}
else
{
lean_dec_ref(v_fvars_2743_);
lean_dec_ref(v_post_2739_);
lean_dec_ref(v_pre_2738_);
return v___x_2769_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_pre_2776_, lean_object* v_post_2777_, uint8_t v_usedLetOnly_2778_, uint8_t v_skipConstInApp_2779_, uint8_t v_skipInstances_2780_, size_t v_sz_2781_, size_t v_i_2782_, lean_object* v_bs_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_usize_dec_lt(v_i_2782_, v_sz_2781_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref(v_post_2777_);
lean_dec_ref(v_pre_2776_);
v___x_2791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2791_, 0, v_bs_2783_);
return v___x_2791_;
}
else
{
lean_object* v_v_2792_; lean_object* v___x_2793_; 
v_v_2792_ = lean_array_uget_borrowed(v_bs_2783_, v_i_2782_);
lean_inc(v_v_2792_);
lean_inc_ref(v_post_2777_);
lean_inc_ref(v_pre_2776_);
v___x_2793_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2776_, v_post_2777_, v_usedLetOnly_2778_, v_skipConstInApp_2779_, v_skipInstances_2780_, v_v_2792_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v_bs_x27_2796_; size_t v___x_2797_; size_t v___x_2798_; lean_object* v___x_2799_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v___x_2795_ = lean_unsigned_to_nat(0u);
v_bs_x27_2796_ = lean_array_uset(v_bs_2783_, v_i_2782_, v___x_2795_);
v___x_2797_ = ((size_t)1ULL);
v___x_2798_ = lean_usize_add(v_i_2782_, v___x_2797_);
v___x_2799_ = lean_array_uset(v_bs_x27_2796_, v_i_2782_, v_a_2794_);
v_i_2782_ = v___x_2798_;
v_bs_2783_ = v___x_2799_;
goto _start;
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec_ref(v_bs_2783_);
lean_dec_ref(v_post_2777_);
lean_dec_ref(v_pre_2776_);
v_a_2801_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2793_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2793_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_2809_, lean_object* v_post_2810_, uint8_t v_usedLetOnly_2811_, uint8_t v_skipConstInApp_2812_, uint8_t v_skipInstances_2813_, lean_object* v___x_2814_, lean_object* v___y_2815_, lean_object* v_b_2816_, lean_object* v_a_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2809_, v_post_2810_, v_usedLetOnly_2811_, v_skipConstInApp_2812_, v_skipInstances_2813_, v___x_2814_, v___y_2815_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2833_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2826_ = v___x_2823_;
v_isShared_2827_ = v_isSharedCheck_2833_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2823_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2833_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2828_ = lean_array_fset(v_b_2816_, v_a_2817_, v_a_2824_);
v___x_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 0, v___x_2829_);
v___x_2831_ = v___x_2826_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec_ref(v_b_2816_);
v_a_2834_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2823_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2823_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_2842_, lean_object* v_post_2843_, lean_object* v_usedLetOnly_2844_, lean_object* v_skipConstInApp_2845_, lean_object* v_skipInstances_2846_, lean_object* v___x_2847_, lean_object* v___y_2848_, lean_object* v_b_2849_, lean_object* v_a_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
uint8_t v_usedLetOnly_boxed_2856_; uint8_t v_skipConstInApp_boxed_2857_; uint8_t v_skipInstances_boxed_2858_; lean_object* v_res_2859_; 
v_usedLetOnly_boxed_2856_ = lean_unbox(v_usedLetOnly_2844_);
v_skipConstInApp_boxed_2857_ = lean_unbox(v_skipConstInApp_2845_);
v_skipInstances_boxed_2858_ = lean_unbox(v_skipInstances_2846_);
v_res_2859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2842_, v_post_2843_, v_usedLetOnly_boxed_2856_, v_skipConstInApp_boxed_2857_, v_skipInstances_boxed_2858_, v___x_2847_, v___y_2848_, v_b_2849_, v_a_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v_a_2850_);
lean_dec(v___y_2848_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object* v_upperBound_2860_, lean_object* v___x_2861_, lean_object* v_pre_2862_, lean_object* v_post_2863_, uint8_t v_usedLetOnly_2864_, uint8_t v_skipConstInApp_2865_, uint8_t v_skipInstances_2866_, lean_object* v_a_2867_, lean_object* v_b_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v___y_2876_; uint8_t v___x_2899_; 
v___x_2899_ = lean_nat_dec_lt(v_a_2867_, v_upperBound_2860_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; 
lean_dec(v_a_2867_);
lean_dec_ref(v_post_2863_);
lean_dec_ref(v_pre_2862_);
v___x_2900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2900_, 0, v_b_2868_);
return v___x_2900_;
}
else
{
lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2901_ = lean_array_fget_borrowed(v_b_2868_, v_a_2867_);
v___x_2902_ = lean_array_get_size(v___x_2861_);
v___x_2903_ = lean_nat_dec_lt(v_a_2867_, v___x_2902_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___f_2907_; 
lean_inc(v___x_2901_);
v___x_2904_ = lean_box(v_usedLetOnly_2864_);
v___x_2905_ = lean_box(v_skipConstInApp_2865_);
v___x_2906_ = lean_box(v_skipInstances_2866_);
lean_inc(v_a_2867_);
lean_inc(v___y_2869_);
lean_inc_ref(v_post_2863_);
lean_inc_ref(v_pre_2862_);
v___f_2907_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2907_, 0, v_pre_2862_);
lean_closure_set(v___f_2907_, 1, v_post_2863_);
lean_closure_set(v___f_2907_, 2, v___x_2904_);
lean_closure_set(v___f_2907_, 3, v___x_2905_);
lean_closure_set(v___f_2907_, 4, v___x_2906_);
lean_closure_set(v___f_2907_, 5, v___x_2901_);
lean_closure_set(v___f_2907_, 6, v___y_2869_);
lean_closure_set(v___f_2907_, 7, v_b_2868_);
lean_closure_set(v___f_2907_, 8, v_a_2867_);
v___y_2876_ = v___f_2907_;
goto v___jp_2875_;
}
else
{
lean_object* v___x_2908_; uint8_t v_isInstance_2909_; 
v___x_2908_ = lean_array_fget_borrowed(v___x_2861_, v_a_2867_);
v_isInstance_2909_ = lean_ctor_get_uint8(v___x_2908_, sizeof(void*)*1 + 4);
if (v_isInstance_2909_ == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___f_2913_; 
lean_inc(v___x_2901_);
v___x_2910_ = lean_box(v_usedLetOnly_2864_);
v___x_2911_ = lean_box(v_skipConstInApp_2865_);
v___x_2912_ = lean_box(v_skipInstances_2866_);
lean_inc(v_a_2867_);
lean_inc(v___y_2869_);
lean_inc_ref(v_post_2863_);
lean_inc_ref(v_pre_2862_);
v___f_2913_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2913_, 0, v_pre_2862_);
lean_closure_set(v___f_2913_, 1, v_post_2863_);
lean_closure_set(v___f_2913_, 2, v___x_2910_);
lean_closure_set(v___f_2913_, 3, v___x_2911_);
lean_closure_set(v___f_2913_, 4, v___x_2912_);
lean_closure_set(v___f_2913_, 5, v___x_2901_);
lean_closure_set(v___f_2913_, 6, v___y_2869_);
lean_closure_set(v___f_2913_, 7, v_b_2868_);
lean_closure_set(v___f_2913_, 8, v_a_2867_);
v___y_2876_ = v___f_2913_;
goto v___jp_2875_;
}
else
{
lean_object* v___x_2914_; lean_object* v___f_2915_; 
v___x_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2914_, 0, v_b_2868_);
v___f_2915_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2915_, 0, v___x_2914_);
v___y_2876_ = v___f_2915_;
goto v___jp_2875_;
}
}
}
v___jp_2875_:
{
lean_object* v___x_2877_; 
lean_inc(v___y_2873_);
lean_inc_ref(v___y_2872_);
lean_inc(v___y_2871_);
lean_inc_ref(v___y_2870_);
v___x_2877_ = lean_apply_5(v___y_2876_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, lean_box(0));
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2890_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2890_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2890_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
if (lean_obj_tag(v_a_2878_) == 0)
{
lean_object* v_a_2882_; lean_object* v___x_2884_; 
lean_dec(v_a_2867_);
lean_dec_ref(v_post_2863_);
lean_dec_ref(v_pre_2862_);
v_a_2882_ = lean_ctor_get(v_a_2878_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v_a_2878_, 1);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v_a_2882_);
v___x_2884_ = v___x_2880_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
lean_del_object(v___x_2880_);
v_a_2886_ = lean_ctor_get(v_a_2878_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v_a_2878_, 1);
v___x_2887_ = lean_unsigned_to_nat(1u);
v___x_2888_ = lean_nat_add(v_a_2867_, v___x_2887_);
lean_dec(v_a_2867_);
v_a_2867_ = v___x_2888_;
v_b_2868_ = v_a_2886_;
goto _start;
}
}
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_a_2867_);
lean_dec_ref(v_post_2863_);
lean_dec_ref(v_pre_2862_);
v_a_2891_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2877_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2877_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2916_, lean_object* v_pre_2917_, lean_object* v_post_2918_, uint8_t v_usedLetOnly_2919_, uint8_t v_skipConstInApp_2920_, lean_object* v_x_2921_, lean_object* v_x_2922_, lean_object* v_x_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_f_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; 
if (lean_obj_tag(v_x_2921_) == 5)
{
lean_object* v_fn_2979_; lean_object* v_arg_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_fn_2979_ = lean_ctor_get(v_x_2921_, 0);
lean_inc_ref(v_fn_2979_);
v_arg_2980_ = lean_ctor_get(v_x_2921_, 1);
lean_inc_ref(v_arg_2980_);
lean_dec_ref_known(v_x_2921_, 2);
v___x_2981_ = lean_array_set(v_x_2922_, v_x_2923_, v_arg_2980_);
v___x_2982_ = lean_unsigned_to_nat(1u);
v___x_2983_ = lean_nat_sub(v_x_2923_, v___x_2982_);
lean_dec(v_x_2923_);
v_x_2921_ = v_fn_2979_;
v_x_2922_ = v___x_2981_;
v_x_2923_ = v___x_2983_;
goto _start;
}
else
{
lean_dec(v_x_2923_);
if (v_skipConstInApp_2920_ == 0)
{
goto v___jp_2976_;
}
else
{
uint8_t v___x_2985_; 
v___x_2985_ = l_Lean_Expr_isConst(v_x_2921_);
if (v___x_2985_ == 0)
{
goto v___jp_2976_;
}
else
{
v_f_2931_ = v_x_2921_;
v___y_2932_ = v___y_2924_;
v___y_2933_ = v___y_2925_;
v___y_2934_ = v___y_2926_;
v___y_2935_ = v___y_2927_;
v___y_2936_ = v___y_2928_;
goto v___jp_2930_;
}
}
}
v___jp_2930_:
{
if (v_skipInstances_2916_ == 0)
{
size_t v_sz_2937_; size_t v___x_2938_; lean_object* v___x_2939_; 
v_sz_2937_ = lean_array_size(v_x_2922_);
v___x_2938_ = ((size_t)0ULL);
lean_inc_ref(v_post_2918_);
lean_inc_ref(v_pre_2917_);
v___x_2939_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2917_, v_post_2918_, v_usedLetOnly_2919_, v_skipConstInApp_2920_, v_skipInstances_2916_, v_sz_2937_, v___x_2938_, v_x_2922_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v___x_2941_ = l_Lean_mkAppN(v_f_2931_, v_a_2940_);
lean_dec(v_a_2940_);
v___x_2942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2917_, v_post_2918_, v_usedLetOnly_2919_, v_skipConstInApp_2920_, v_skipInstances_2916_, v___x_2941_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2942_;
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_f_2931_);
lean_dec_ref(v_post_2918_);
lean_dec_ref(v_pre_2917_);
v_a_2943_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2939_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2939_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
else
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_array_get_size(v_x_2922_);
lean_inc_ref(v_f_2931_);
v___x_2952_ = l_Lean_Meta_getFunInfoNArgs(v_f_2931_, v___x_2951_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v_paramInfo_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v_paramInfo_2954_ = lean_ctor_get(v_a_2953_, 0);
lean_inc_ref(v_paramInfo_2954_);
lean_dec(v_a_2953_);
v___x_2955_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2918_);
lean_inc_ref(v_pre_2917_);
v___x_2956_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v___x_2951_, v_paramInfo_2954_, v_pre_2917_, v_post_2918_, v_usedLetOnly_2919_, v_skipConstInApp_2920_, v_skipInstances_2916_, v___x_2955_, v_x_2922_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec_ref(v_paramInfo_2954_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = l_Lean_mkAppN(v_f_2931_, v_a_2957_);
lean_dec(v_a_2957_);
v___x_2959_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2917_, v_post_2918_, v_usedLetOnly_2919_, v_skipConstInApp_2920_, v_skipInstances_2916_, v___x_2958_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2959_;
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v_f_2931_);
lean_dec_ref(v_post_2918_);
lean_dec_ref(v_pre_2917_);
v_a_2960_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2956_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2956_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec_ref(v_f_2931_);
lean_dec_ref(v_x_2922_);
lean_dec_ref(v_post_2918_);
lean_dec_ref(v_pre_2917_);
v_a_2968_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2952_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2952_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
}
v___jp_2976_:
{
lean_object* v___x_2977_; 
lean_inc_ref(v_post_2918_);
lean_inc_ref(v_pre_2917_);
v___x_2977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2917_, v_post_2918_, v_usedLetOnly_2919_, v_skipConstInApp_2920_, v_skipInstances_2916_, v_x_2921_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v_f_2931_ = v_a_2978_;
v___y_2932_ = v___y_2924_;
v___y_2933_ = v___y_2925_;
v___y_2934_ = v___y_2926_;
v___y_2935_ = v___y_2927_;
v___y_2936_ = v___y_2928_;
goto v___jp_2930_;
}
else
{
lean_dec_ref(v_x_2922_);
lean_dec_ref(v_post_2918_);
lean_dec_ref(v_pre_2917_);
return v___x_2977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v___x_2986_, lean_object* v_pre_2987_, lean_object* v_e_2988_, lean_object* v_post_2989_, uint8_t v_usedLetOnly_2990_, uint8_t v_skipConstInApp_2991_, uint8_t v_skipInstances_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_Core_checkSystem(v___x_2986_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3000_; 
lean_dec_ref_known(v___x_2999_, 1);
lean_inc_ref(v_pre_2987_);
lean_inc(v___y_2997_);
lean_inc_ref(v___y_2996_);
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc_ref(v_e_2988_);
v___x_3000_ = lean_apply_6(v_pre_2987_, v_e_2988_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, lean_box(0));
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3049_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3049_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3049_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___y_3006_; 
switch(lean_obj_tag(v_a_3001_))
{
case 0:
{
lean_object* v_e_3041_; lean_object* v___x_3043_; 
lean_dec_ref(v_post_2989_);
lean_dec_ref(v_e_2988_);
lean_dec_ref(v_pre_2987_);
v_e_3041_ = lean_ctor_get(v_a_3001_, 0);
lean_inc_ref(v_e_3041_);
lean_dec_ref_known(v_a_3001_, 1);
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v_e_3041_);
v___x_3043_ = v___x_3003_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_e_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
case 1:
{
lean_object* v_e_3045_; lean_object* v___x_3046_; 
lean_del_object(v___x_3003_);
lean_dec_ref(v_e_2988_);
v_e_3045_ = lean_ctor_get(v_a_3001_, 0);
lean_inc_ref(v_e_3045_);
lean_dec_ref_known(v_a_3001_, 1);
v___x_3046_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v_e_3045_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3046_;
}
default: 
{
lean_object* v_e_x3f_3047_; 
lean_del_object(v___x_3003_);
v_e_x3f_3047_ = lean_ctor_get(v_a_3001_, 0);
lean_inc(v_e_x3f_3047_);
lean_dec_ref_known(v_a_3001_, 1);
if (lean_obj_tag(v_e_x3f_3047_) == 0)
{
v___y_3006_ = v_e_2988_;
goto v___jp_3005_;
}
else
{
lean_object* v_val_3048_; 
lean_dec_ref(v_e_2988_);
v_val_3048_ = lean_ctor_get(v_e_x3f_3047_, 0);
lean_inc(v_val_3048_);
lean_dec_ref_known(v_e_x3f_3047_, 1);
v___y_3006_ = v_val_3048_;
goto v___jp_3005_;
}
}
}
v___jp_3005_:
{
switch(lean_obj_tag(v___y_3006_))
{
case 7:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___x_3007_, v___y_3006_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3008_;
}
case 6:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___x_3009_, v___y_3006_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3010_;
}
case 8:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3012_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___x_3011_, v___y_3006_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3012_;
}
case 5:
{
lean_object* v_dummy_3013_; lean_object* v_nargs_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v_dummy_3013_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3014_ = l_Lean_Expr_getAppNumArgs(v___y_3006_);
lean_inc(v_nargs_3014_);
v___x_3015_ = lean_mk_array(v_nargs_3014_, v_dummy_3013_);
v___x_3016_ = lean_unsigned_to_nat(1u);
v___x_3017_ = lean_nat_sub(v_nargs_3014_, v___x_3016_);
lean_dec(v_nargs_3014_);
v___x_3018_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_2992_, v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v___y_3006_, v___x_3015_, v___x_3017_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3018_;
}
case 10:
{
lean_object* v_data_3019_; lean_object* v_expr_3020_; lean_object* v___x_3021_; 
v_data_3019_ = lean_ctor_get(v___y_3006_, 0);
v_expr_3020_ = lean_ctor_get(v___y_3006_, 1);
lean_inc_ref(v_expr_3020_);
lean_inc_ref(v_post_2989_);
lean_inc_ref(v_pre_2987_);
v___x_3021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v_expr_3020_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; size_t v___x_3023_; size_t v___x_3024_; uint8_t v___x_3025_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = lean_ptr_addr(v_expr_3020_);
v___x_3024_ = lean_ptr_addr(v_a_3022_);
v___x_3025_ = lean_usize_dec_eq(v___x_3023_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v___x_3027_; 
lean_inc(v_data_3019_);
lean_dec_ref_known(v___y_3006_, 2);
v___x_3026_ = l_Lean_Expr_mdata___override(v_data_3019_, v_a_3022_);
v___x_3027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___x_3026_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; 
lean_dec(v_a_3022_);
v___x_3028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___y_3006_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3028_;
}
}
else
{
lean_dec_ref_known(v___y_3006_, 2);
lean_dec_ref(v_post_2989_);
lean_dec_ref(v_pre_2987_);
return v___x_3021_;
}
}
case 11:
{
lean_object* v_typeName_3029_; lean_object* v_idx_3030_; lean_object* v_struct_3031_; lean_object* v___x_3032_; 
v_typeName_3029_ = lean_ctor_get(v___y_3006_, 0);
v_idx_3030_ = lean_ctor_get(v___y_3006_, 1);
v_struct_3031_ = lean_ctor_get(v___y_3006_, 2);
lean_inc_ref(v_struct_3031_);
lean_inc_ref(v_post_2989_);
lean_inc_ref(v_pre_2987_);
v___x_3032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v_struct_3031_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; size_t v___x_3034_; size_t v___x_3035_; uint8_t v___x_3036_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = lean_ptr_addr(v_struct_3031_);
v___x_3035_ = lean_ptr_addr(v_a_3033_);
v___x_3036_ = lean_usize_dec_eq(v___x_3034_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
lean_inc(v_idx_3030_);
lean_inc(v_typeName_3029_);
lean_dec_ref_known(v___y_3006_, 3);
v___x_3037_ = l_Lean_Expr_proj___override(v_typeName_3029_, v_idx_3030_, v_a_3033_);
v___x_3038_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___x_3037_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; 
lean_dec(v_a_3033_);
v___x_3039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___y_3006_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3039_;
}
}
else
{
lean_dec_ref_known(v___y_3006_, 3);
lean_dec_ref(v_post_2989_);
lean_dec_ref(v_pre_2987_);
return v___x_3032_;
}
}
default: 
{
lean_object* v___x_3040_; 
v___x_3040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2987_, v_post_2989_, v_usedLetOnly_2990_, v_skipConstInApp_2991_, v_skipInstances_2992_, v___y_3006_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3040_;
}
}
}
}
}
else
{
lean_object* v_a_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3057_; 
lean_dec_ref(v_post_2989_);
lean_dec_ref(v_e_2988_);
lean_dec_ref(v_pre_2987_);
v_a_3050_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3057_ == 0)
{
v___x_3052_ = v___x_3000_;
v_isShared_3053_ = v_isSharedCheck_3057_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_a_3050_);
lean_dec(v___x_3000_);
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
lean_dec_ref(v_post_2989_);
lean_dec_ref(v_e_2988_);
lean_dec_ref(v_pre_2987_);
v_a_3058_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_2999_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_2999_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v___x_3066_, lean_object* v_pre_3067_, lean_object* v_e_3068_, lean_object* v_post_3069_, lean_object* v_usedLetOnly_3070_, lean_object* v_skipConstInApp_3071_, lean_object* v_skipInstances_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
uint8_t v_usedLetOnly_boxed_3079_; uint8_t v_skipConstInApp_boxed_3080_; uint8_t v_skipInstances_boxed_3081_; lean_object* v_res_3082_; 
v_usedLetOnly_boxed_3079_ = lean_unbox(v_usedLetOnly_3070_);
v_skipConstInApp_boxed_3080_ = lean_unbox(v_skipConstInApp_3071_);
v_skipInstances_boxed_3081_ = lean_unbox(v_skipInstances_3072_);
v_res_3082_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v___x_3066_, v_pre_3067_, v_e_3068_, v_post_3069_, v_usedLetOnly_boxed_3079_, v_skipConstInApp_boxed_3080_, v_skipInstances_boxed_3081_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3083_, lean_object* v_post_3084_, uint8_t v_usedLetOnly_3085_, uint8_t v_skipConstInApp_3086_, uint8_t v_skipInstances_3087_, lean_object* v_e_3088_, lean_object* v_a_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; 
lean_inc(v_a_3089_);
v___x_3095_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3095_, 0, lean_box(0));
lean_closure_set(v___x_3095_, 1, lean_box(0));
lean_closure_set(v___x_3095_, 2, v_a_3089_);
v___x_3096_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3095_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3096_) == 0)
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3131_; 
v_a_3097_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3099_ = v___x_3096_;
v_isShared_3100_ = v_isSharedCheck_3131_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3131_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3097_, v_e_3088_);
lean_dec(v_a_3097_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___f_3106_; lean_object* v___x_3107_; 
lean_del_object(v___x_3099_);
v___x_3102_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
v___x_3103_ = lean_box(v_usedLetOnly_3085_);
v___x_3104_ = lean_box(v_skipConstInApp_3086_);
v___x_3105_ = lean_box(v_skipInstances_3087_);
lean_inc_ref(v_e_3088_);
v___f_3106_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3106_, 0, v___x_3102_);
lean_closure_set(v___f_3106_, 1, v_pre_3083_);
lean_closure_set(v___f_3106_, 2, v_e_3088_);
lean_closure_set(v___f_3106_, 3, v_post_3084_);
lean_closure_set(v___f_3106_, 4, v___x_3103_);
lean_closure_set(v___f_3106_, 5, v___x_3104_);
lean_closure_set(v___f_3106_, 6, v___x_3105_);
v___x_3107_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3106_, v_a_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v___f_3109_; lean_object* v___x_3110_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc_n(v_a_3108_, 2);
lean_dec_ref_known(v___x_3107_, 1);
lean_inc(v_a_3089_);
v___f_3109_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3109_, 0, v_a_3089_);
lean_closure_set(v___f_3109_, 1, v_e_3088_);
lean_closure_set(v___f_3109_, 2, v_a_3108_);
v___x_3110_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3109_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_3110_, 0);
lean_dec(v_unused_3118_);
v___x_3112_ = v___x_3110_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_dec(v___x_3110_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v_a_3108_);
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3108_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_a_3108_);
v_a_3119_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3110_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3110_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_dec_ref(v_e_3088_);
return v___x_3107_;
}
}
else
{
lean_object* v_val_3127_; lean_object* v___x_3129_; 
lean_dec_ref(v_e_3088_);
lean_dec_ref(v_post_3084_);
lean_dec_ref(v_pre_3083_);
v_val_3127_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3101_, 1);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 0, v_val_3127_);
v___x_3129_ = v___x_3099_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_val_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v_e_3088_);
lean_dec_ref(v_post_3084_);
lean_dec_ref(v_pre_3083_);
v_a_3132_ = lean_ctor_get(v___x_3096_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3096_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3096_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3096_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_3140_, lean_object* v_pre_3141_, lean_object* v_post_3142_, lean_object* v_usedLetOnly_3143_, lean_object* v_skipConstInApp_3144_, lean_object* v_skipInstances_3145_, lean_object* v_body_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
uint8_t v_usedLetOnly_boxed_3154_; uint8_t v_skipConstInApp_boxed_3155_; uint8_t v_skipInstances_boxed_3156_; lean_object* v_res_3157_; 
v_usedLetOnly_boxed_3154_ = lean_unbox(v_usedLetOnly_3143_);
v_skipConstInApp_boxed_3155_ = lean_unbox(v_skipConstInApp_3144_);
v_skipInstances_boxed_3156_ = lean_unbox(v_skipInstances_3145_);
v_res_3157_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_3140_, v_pre_3141_, v_post_3142_, v_usedLetOnly_boxed_3154_, v_skipConstInApp_boxed_3155_, v_skipInstances_boxed_3156_, v_body_3146_, v_x_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3148_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3158_, lean_object* v_post_3159_, uint8_t v_usedLetOnly_3160_, uint8_t v_skipConstInApp_3161_, uint8_t v_skipInstances_3162_, lean_object* v_fvars_3163_, lean_object* v_e_3164_, lean_object* v_a_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
if (lean_obj_tag(v_e_3164_) == 7)
{
lean_object* v_binderName_3171_; lean_object* v_binderType_3172_; lean_object* v_body_3173_; uint8_t v_binderInfo_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v_binderName_3171_ = lean_ctor_get(v_e_3164_, 0);
lean_inc(v_binderName_3171_);
v_binderType_3172_ = lean_ctor_get(v_e_3164_, 1);
lean_inc_ref(v_binderType_3172_);
v_body_3173_ = lean_ctor_get(v_e_3164_, 2);
lean_inc_ref(v_body_3173_);
v_binderInfo_3174_ = lean_ctor_get_uint8(v_e_3164_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3164_, 3);
v___x_3175_ = lean_expr_instantiate_rev(v_binderType_3172_, v_fvars_3163_);
lean_dec_ref(v_binderType_3172_);
lean_inc_ref(v_post_3159_);
lean_inc_ref(v_pre_3158_);
v___x_3176_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3158_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___x_3175_, v_a_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___f_3181_; uint8_t v___x_3182_; lean_object* v___x_3183_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3176_, 1);
v___x_3178_ = lean_box(v_usedLetOnly_3160_);
v___x_3179_ = lean_box(v_skipConstInApp_3161_);
v___x_3180_ = lean_box(v_skipInstances_3162_);
v___f_3181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3181_, 0, v_fvars_3163_);
lean_closure_set(v___f_3181_, 1, v_pre_3158_);
lean_closure_set(v___f_3181_, 2, v_post_3159_);
lean_closure_set(v___f_3181_, 3, v___x_3178_);
lean_closure_set(v___f_3181_, 4, v___x_3179_);
lean_closure_set(v___f_3181_, 5, v___x_3180_);
lean_closure_set(v___f_3181_, 6, v_body_3173_);
v___x_3182_ = 0;
v___x_3183_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3171_, v_binderInfo_3174_, v_a_3177_, v___f_3181_, v___x_3182_, v_a_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
return v___x_3183_;
}
else
{
lean_dec_ref(v_body_3173_);
lean_dec(v_binderName_3171_);
lean_dec_ref(v_fvars_3163_);
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_pre_3158_);
return v___x_3176_;
}
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_expr_instantiate_rev(v_e_3164_, v_fvars_3163_);
lean_dec_ref(v_e_3164_);
lean_inc_ref(v_post_3159_);
lean_inc_ref(v_pre_3158_);
v___x_3185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3158_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v___x_3184_, v_a_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; uint8_t v___x_3187_; uint8_t v___x_3188_; uint8_t v___x_3189_; lean_object* v___x_3190_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = 0;
v___x_3188_ = 1;
v___x_3189_ = 1;
v___x_3190_ = l_Lean_Meta_mkForallFVars(v_fvars_3163_, v_a_3186_, v___x_3187_, v_usedLetOnly_3160_, v___x_3188_, v___x_3189_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec_ref(v_fvars_3163_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3158_, v_post_3159_, v_usedLetOnly_3160_, v_skipConstInApp_3161_, v_skipInstances_3162_, v_a_3191_, v_a_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
return v___x_3192_;
}
else
{
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_pre_3158_);
return v___x_3190_;
}
}
else
{
lean_dec_ref(v_fvars_3163_);
lean_dec_ref(v_post_3159_);
lean_dec_ref(v_pre_3158_);
return v___x_3185_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3193_, lean_object* v_pre_3194_, lean_object* v_post_3195_, uint8_t v_usedLetOnly_3196_, uint8_t v_skipConstInApp_3197_, uint8_t v_skipInstances_3198_, lean_object* v_body_3199_, lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = lean_array_push(v_fvars_3193_, v_x_3200_);
v___x_3208_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3194_, v_post_3195_, v_usedLetOnly_3196_, v_skipConstInApp_3197_, v_skipInstances_3198_, v___x_3207_, v_body_3199_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3209_, lean_object* v_post_3210_, lean_object* v_usedLetOnly_3211_, lean_object* v_skipConstInApp_3212_, lean_object* v_skipInstances_3213_, lean_object* v_e_3214_, lean_object* v_a_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v_usedLetOnly_boxed_3221_; uint8_t v_skipConstInApp_boxed_3222_; uint8_t v_skipInstances_boxed_3223_; lean_object* v_res_3224_; 
v_usedLetOnly_boxed_3221_ = lean_unbox(v_usedLetOnly_3211_);
v_skipConstInApp_boxed_3222_ = lean_unbox(v_skipConstInApp_3212_);
v_skipInstances_boxed_3223_ = lean_unbox(v_skipInstances_3213_);
v_res_3224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3209_, v_post_3210_, v_usedLetOnly_boxed_3221_, v_skipConstInApp_boxed_3222_, v_skipInstances_boxed_3223_, v_e_3214_, v_a_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v_a_3215_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_pre_3225_, lean_object* v_post_3226_, lean_object* v_usedLetOnly_3227_, lean_object* v_skipConstInApp_3228_, lean_object* v_skipInstances_3229_, lean_object* v_sz_3230_, lean_object* v_i_3231_, lean_object* v_bs_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
uint8_t v_usedLetOnly_boxed_3239_; uint8_t v_skipConstInApp_boxed_3240_; uint8_t v_skipInstances_boxed_3241_; size_t v_sz_boxed_3242_; size_t v_i_boxed_3243_; lean_object* v_res_3244_; 
v_usedLetOnly_boxed_3239_ = lean_unbox(v_usedLetOnly_3227_);
v_skipConstInApp_boxed_3240_ = lean_unbox(v_skipConstInApp_3228_);
v_skipInstances_boxed_3241_ = lean_unbox(v_skipInstances_3229_);
v_sz_boxed_3242_ = lean_unbox_usize(v_sz_3230_);
lean_dec(v_sz_3230_);
v_i_boxed_3243_ = lean_unbox_usize(v_i_3231_);
lean_dec(v_i_3231_);
v_res_3244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_3225_, v_post_3226_, v_usedLetOnly_boxed_3239_, v_skipConstInApp_boxed_3240_, v_skipInstances_boxed_3241_, v_sz_boxed_3242_, v_i_boxed_3243_, v_bs_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
lean_dec(v___y_3233_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3245_, lean_object* v_post_3246_, lean_object* v_usedLetOnly_3247_, lean_object* v_skipConstInApp_3248_, lean_object* v_skipInstances_3249_, lean_object* v_e_3250_, lean_object* v_a_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
uint8_t v_usedLetOnly_boxed_3257_; uint8_t v_skipConstInApp_boxed_3258_; uint8_t v_skipInstances_boxed_3259_; lean_object* v_res_3260_; 
v_usedLetOnly_boxed_3257_ = lean_unbox(v_usedLetOnly_3247_);
v_skipConstInApp_boxed_3258_ = lean_unbox(v_skipConstInApp_3248_);
v_skipInstances_boxed_3259_ = lean_unbox(v_skipInstances_3249_);
v_res_3260_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3245_, v_post_3246_, v_usedLetOnly_boxed_3257_, v_skipConstInApp_boxed_3258_, v_skipInstances_boxed_3259_, v_e_3250_, v_a_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v_a_3251_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3261_, lean_object* v_post_3262_, lean_object* v_usedLetOnly_3263_, lean_object* v_skipConstInApp_3264_, lean_object* v_skipInstances_3265_, lean_object* v_fvars_3266_, lean_object* v_e_3267_, lean_object* v_a_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v_usedLetOnly_boxed_3274_; uint8_t v_skipConstInApp_boxed_3275_; uint8_t v_skipInstances_boxed_3276_; lean_object* v_res_3277_; 
v_usedLetOnly_boxed_3274_ = lean_unbox(v_usedLetOnly_3263_);
v_skipConstInApp_boxed_3275_ = lean_unbox(v_skipConstInApp_3264_);
v_skipInstances_boxed_3276_ = lean_unbox(v_skipInstances_3265_);
v_res_3277_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3261_, v_post_3262_, v_usedLetOnly_boxed_3274_, v_skipConstInApp_boxed_3275_, v_skipInstances_boxed_3276_, v_fvars_3266_, v_e_3267_, v_a_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v_a_3268_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3278_, lean_object* v_post_3279_, lean_object* v_usedLetOnly_3280_, lean_object* v_skipConstInApp_3281_, lean_object* v_skipInstances_3282_, lean_object* v_fvars_3283_, lean_object* v_e_3284_, lean_object* v_a_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
uint8_t v_usedLetOnly_boxed_3291_; uint8_t v_skipConstInApp_boxed_3292_; uint8_t v_skipInstances_boxed_3293_; lean_object* v_res_3294_; 
v_usedLetOnly_boxed_3291_ = lean_unbox(v_usedLetOnly_3280_);
v_skipConstInApp_boxed_3292_ = lean_unbox(v_skipConstInApp_3281_);
v_skipInstances_boxed_3293_ = lean_unbox(v_skipInstances_3282_);
v_res_3294_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3278_, v_post_3279_, v_usedLetOnly_boxed_3291_, v_skipConstInApp_boxed_3292_, v_skipInstances_boxed_3293_, v_fvars_3283_, v_e_3284_, v_a_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v_a_3285_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3295_, lean_object* v_post_3296_, lean_object* v_usedLetOnly_3297_, lean_object* v_skipConstInApp_3298_, lean_object* v_skipInstances_3299_, lean_object* v_fvars_3300_, lean_object* v_e_3301_, lean_object* v_a_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v_usedLetOnly_boxed_3308_; uint8_t v_skipConstInApp_boxed_3309_; uint8_t v_skipInstances_boxed_3310_; lean_object* v_res_3311_; 
v_usedLetOnly_boxed_3308_ = lean_unbox(v_usedLetOnly_3297_);
v_skipConstInApp_boxed_3309_ = lean_unbox(v_skipConstInApp_3298_);
v_skipInstances_boxed_3310_ = lean_unbox(v_skipInstances_3299_);
v_res_3311_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3295_, v_post_3296_, v_usedLetOnly_boxed_3308_, v_skipConstInApp_boxed_3309_, v_skipInstances_boxed_3310_, v_fvars_3300_, v_e_3301_, v_a_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v_a_3302_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3312_, lean_object* v___x_3313_, lean_object* v_pre_3314_, lean_object* v_post_3315_, lean_object* v_usedLetOnly_3316_, lean_object* v_skipConstInApp_3317_, lean_object* v_skipInstances_3318_, lean_object* v_a_3319_, lean_object* v_b_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
uint8_t v_usedLetOnly_boxed_3327_; uint8_t v_skipConstInApp_boxed_3328_; uint8_t v_skipInstances_boxed_3329_; lean_object* v_res_3330_; 
v_usedLetOnly_boxed_3327_ = lean_unbox(v_usedLetOnly_3316_);
v_skipConstInApp_boxed_3328_ = lean_unbox(v_skipConstInApp_3317_);
v_skipInstances_boxed_3329_ = lean_unbox(v_skipInstances_3318_);
v_res_3330_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3312_, v___x_3313_, v_pre_3314_, v_post_3315_, v_usedLetOnly_boxed_3327_, v_skipConstInApp_boxed_3328_, v_skipInstances_boxed_3329_, v_a_3319_, v_b_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___x_3313_);
lean_dec(v_upperBound_3312_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3331_, lean_object* v_pre_3332_, lean_object* v_post_3333_, lean_object* v_usedLetOnly_3334_, lean_object* v_skipConstInApp_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_, lean_object* v_x_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
uint8_t v_skipInstances_boxed_3345_; uint8_t v_usedLetOnly_boxed_3346_; uint8_t v_skipConstInApp_boxed_3347_; lean_object* v_res_3348_; 
v_skipInstances_boxed_3345_ = lean_unbox(v_skipInstances_3331_);
v_usedLetOnly_boxed_3346_ = lean_unbox(v_usedLetOnly_3334_);
v_skipConstInApp_boxed_3347_ = lean_unbox(v_skipConstInApp_3335_);
v_res_3348_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3345_, v_pre_3332_, v_post_3333_, v_usedLetOnly_boxed_3346_, v_skipConstInApp_boxed_3347_, v_x_3336_, v_x_3337_, v_x_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v___y_3339_);
return v_res_3348_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_unsigned_to_nat(16u);
v___x_3351_ = lean_mk_array(v___x_3350_, v___x_3349_);
return v___x_3351_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3352_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
lean_ctor_set(v___x_3354_, 1, v___x_3352_);
return v___x_3354_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3355_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3356_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3356_, 0, lean_box(0));
lean_closure_set(v___x_3356_, 1, lean_box(0));
lean_closure_set(v___x_3356_, 2, v___x_3355_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3357_, lean_object* v_pre_3358_, lean_object* v_post_3359_, uint8_t v_usedLetOnly_3360_, uint8_t v_skipConstInApp_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v_a_3369_; uint8_t v___x_3370_; lean_object* v___x_3371_; 
v___x_3367_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3368_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3367_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref(v___x_3368_);
v___x_3370_ = 0;
v___x_3371_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3358_, v_post_3359_, v_usedLetOnly_3360_, v_skipConstInApp_3361_, v___x_3370_, v_input_3357_, v_a_3369_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v_a_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3376_; uint8_t v_isShared_3377_; uint8_t v_isSharedCheck_3381_; 
v_a_3372_ = lean_ctor_get(v___x_3371_, 0);
lean_inc(v_a_3372_);
lean_dec_ref_known(v___x_3371_, 1);
v___x_3373_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3373_, 0, lean_box(0));
lean_closure_set(v___x_3373_, 1, lean_box(0));
lean_closure_set(v___x_3373_, 2, v_a_3369_);
v___x_3374_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3373_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3381_ == 0)
{
lean_object* v_unused_3382_; 
v_unused_3382_ = lean_ctor_get(v___x_3374_, 0);
lean_dec(v_unused_3382_);
v___x_3376_ = v___x_3374_;
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
else
{
lean_dec(v___x_3374_);
v___x_3376_ = lean_box(0);
v_isShared_3377_ = v_isSharedCheck_3381_;
goto v_resetjp_3375_;
}
v_resetjp_3375_:
{
lean_object* v___x_3379_; 
if (v_isShared_3377_ == 0)
{
lean_ctor_set(v___x_3376_, 0, v_a_3372_);
v___x_3379_ = v___x_3376_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v_a_3372_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
else
{
lean_dec(v_a_3369_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3383_, lean_object* v_pre_3384_, lean_object* v_post_3385_, lean_object* v_usedLetOnly_3386_, lean_object* v_skipConstInApp_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
uint8_t v_usedLetOnly_boxed_3393_; uint8_t v_skipConstInApp_boxed_3394_; lean_object* v_res_3395_; 
v_usedLetOnly_boxed_3393_ = lean_unbox(v_usedLetOnly_3386_);
v_skipConstInApp_boxed_3394_ = lean_unbox(v_skipConstInApp_3387_);
v_res_3395_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3383_, v_pre_3384_, v_post_3385_, v_usedLetOnly_boxed_3393_, v_skipConstInApp_boxed_3394_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v___f_3404_; lean_object* v___f_3405_; uint8_t v___x_3406_; lean_object* v___x_3407_; 
v___f_3404_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3405_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3406_ = 0;
v___x_3407_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3398_, v___f_3405_, v___f_3404_, v___x_3406_, v___x_3406_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v_res_3414_; 
v_res_3414_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_);
lean_dec(v_a_3412_);
lean_dec_ref(v_a_3411_);
lean_dec(v_a_3410_);
lean_dec_ref(v_a_3409_);
return v_res_3414_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_upperBound_3415_, lean_object* v___x_3416_, lean_object* v_pre_3417_, lean_object* v_post_3418_, uint8_t v_usedLetOnly_3419_, uint8_t v_skipConstInApp_3420_, uint8_t v_skipInstances_3421_, lean_object* v___x_3422_, lean_object* v_inst_3423_, lean_object* v_R_3424_, lean_object* v_a_3425_, lean_object* v_b_3426_, lean_object* v_c_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3415_, v___x_3416_, v_pre_3417_, v_post_3418_, v_usedLetOnly_3419_, v_skipConstInApp_3420_, v_skipInstances_3421_, v_a_3425_, v_b_3426_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_3435_ = _args[0];
lean_object* v___x_3436_ = _args[1];
lean_object* v_pre_3437_ = _args[2];
lean_object* v_post_3438_ = _args[3];
lean_object* v_usedLetOnly_3439_ = _args[4];
lean_object* v_skipConstInApp_3440_ = _args[5];
lean_object* v_skipInstances_3441_ = _args[6];
lean_object* v___x_3442_ = _args[7];
lean_object* v_inst_3443_ = _args[8];
lean_object* v_R_3444_ = _args[9];
lean_object* v_a_3445_ = _args[10];
lean_object* v_b_3446_ = _args[11];
lean_object* v_c_3447_ = _args[12];
lean_object* v___y_3448_ = _args[13];
lean_object* v___y_3449_ = _args[14];
lean_object* v___y_3450_ = _args[15];
lean_object* v___y_3451_ = _args[16];
lean_object* v___y_3452_ = _args[17];
lean_object* v___y_3453_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3454_; uint8_t v_skipConstInApp_boxed_3455_; uint8_t v_skipInstances_boxed_3456_; lean_object* v_res_3457_; 
v_usedLetOnly_boxed_3454_ = lean_unbox(v_usedLetOnly_3439_);
v_skipConstInApp_boxed_3455_ = lean_unbox(v_skipConstInApp_3440_);
v_skipInstances_boxed_3456_ = lean_unbox(v_skipInstances_3441_);
v_res_3457_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3435_, v___x_3436_, v_pre_3437_, v_post_3438_, v_usedLetOnly_boxed_3454_, v_skipConstInApp_boxed_3455_, v_skipInstances_boxed_3456_, v___x_3442_, v_inst_3443_, v_R_3444_, v_a_3445_, v_b_3446_, v_c_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec(v___x_3442_);
lean_dec_ref(v___x_3436_);
lean_dec(v_upperBound_3435_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_00_u03b2_3458_, lean_object* v_m_3459_, lean_object* v_a_3460_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_3459_, v_a_3460_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3462_, lean_object* v_m_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v_res_3465_; 
v_res_3465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_00_u03b2_3462_, v_m_3463_, v_a_3464_);
lean_dec_ref(v_a_3464_);
lean_dec_ref(v_m_3463_);
return v_res_3465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3466_, lean_object* v_name_3467_, uint8_t v_bi_3468_, lean_object* v_type_3469_, lean_object* v_k_3470_, uint8_t v_kind_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3467_, v_bi_3468_, v_type_3469_, v_k_3470_, v_kind_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_, v___y_3476_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_name_3480_, lean_object* v_bi_3481_, lean_object* v_type_3482_, lean_object* v_k_3483_, lean_object* v_kind_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
uint8_t v_bi_boxed_3491_; uint8_t v_kind_boxed_3492_; lean_object* v_res_3493_; 
v_bi_boxed_3491_ = lean_unbox(v_bi_3481_);
v_kind_boxed_3492_ = lean_unbox(v_kind_3484_);
v_res_3493_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3479_, v_name_3480_, v_bi_boxed_3491_, v_type_3482_, v_k_3483_, v_kind_boxed_3492_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec(v___y_3489_);
lean_dec_ref(v___y_3488_);
lean_dec(v___y_3487_);
lean_dec_ref(v___y_3486_);
lean_dec(v___y_3485_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3494_, lean_object* v_name_3495_, lean_object* v_type_3496_, lean_object* v_val_3497_, lean_object* v_k_3498_, uint8_t v_nondep_3499_, uint8_t v_kind_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3495_, v_type_3496_, v_val_3497_, v_k_3498_, v_nondep_3499_, v_kind_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3508_, lean_object* v_name_3509_, lean_object* v_type_3510_, lean_object* v_val_3511_, lean_object* v_k_3512_, lean_object* v_nondep_3513_, lean_object* v_kind_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_){
_start:
{
uint8_t v_nondep_boxed_3521_; uint8_t v_kind_boxed_3522_; lean_object* v_res_3523_; 
v_nondep_boxed_3521_ = lean_unbox(v_nondep_3513_);
v_kind_boxed_3522_ = lean_unbox(v_kind_3514_);
v_res_3523_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3508_, v_name_3509_, v_type_3510_, v_val_3511_, v_k_3512_, v_nondep_boxed_3521_, v_kind_boxed_3522_, v___y_3515_, v___y_3516_, v___y_3517_, v___y_3518_, v___y_3519_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3524_, lean_object* v_ref_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v___x_3531_; 
v___x_3531_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3525_);
return v___x_3531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3532_, lean_object* v_ref_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
lean_object* v_res_3539_; 
v_res_3539_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3532_, v_ref_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3540_, lean_object* v_x_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; 
v___x_3548_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3549_, lean_object* v_x_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3549_, v_x_3550_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3558_, lean_object* v_m_3559_, lean_object* v_a_3560_, lean_object* v_b_3561_){
_start:
{
lean_object* v___x_3562_; 
v___x_3562_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3559_, v_a_3560_, v_b_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3563_, lean_object* v_a_3564_, lean_object* v_x_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_3564_, v_x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b2_3567_, lean_object* v_a_3568_, lean_object* v_x_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(v_00_u03b2_3567_, v_a_3568_, v_x_3569_);
lean_dec(v_x_3569_);
lean_dec_ref(v_a_3568_);
return v_res_3570_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3571_, lean_object* v_a_3572_, lean_object* v_x_3573_){
_start:
{
uint8_t v___x_3574_; 
v___x_3574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3572_, v_x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3575_, lean_object* v_a_3576_, lean_object* v_x_3577_){
_start:
{
uint8_t v_res_3578_; lean_object* v_r_3579_; 
v_res_3578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3575_, v_a_3576_, v_x_3577_);
lean_dec(v_x_3577_);
lean_dec_ref(v_a_3576_);
v_r_3579_ = lean_box(v_res_3578_);
return v_r_3579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3580_, lean_object* v_data_3581_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3581_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3583_, lean_object* v_a_3584_, lean_object* v_b_3585_, lean_object* v_x_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3584_, v_b_3585_, v_x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3588_, lean_object* v_i_3589_, lean_object* v_source_3590_, lean_object* v_target_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3589_, v_source_3590_, v_target_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3593_, lean_object* v_x_3594_, lean_object* v_x_3595_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3594_, v_x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3597_, lean_object* v_opt_3598_){
_start:
{
lean_object* v_name_3599_; lean_object* v_defValue_3600_; lean_object* v_map_3601_; lean_object* v___x_3602_; 
v_name_3599_ = lean_ctor_get(v_opt_3598_, 0);
v_defValue_3600_ = lean_ctor_get(v_opt_3598_, 1);
v_map_3601_ = lean_ctor_get(v_opts_3597_, 0);
v___x_3602_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3601_, v_name_3599_);
if (lean_obj_tag(v___x_3602_) == 0)
{
uint8_t v___x_3603_; 
v___x_3603_ = lean_unbox(v_defValue_3600_);
return v___x_3603_;
}
else
{
lean_object* v_val_3604_; 
v_val_3604_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_val_3604_);
lean_dec_ref_known(v___x_3602_, 1);
if (lean_obj_tag(v_val_3604_) == 1)
{
uint8_t v_v_3605_; 
v_v_3605_ = lean_ctor_get_uint8(v_val_3604_, 0);
lean_dec_ref_known(v_val_3604_, 0);
return v_v_3605_;
}
else
{
uint8_t v___x_3606_; 
lean_dec(v_val_3604_);
v___x_3606_ = lean_unbox(v_defValue_3600_);
return v___x_3606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3607_, lean_object* v_opt_3608_){
_start:
{
uint8_t v_res_3609_; lean_object* v_r_3610_; 
v_res_3609_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3607_, v_opt_3608_);
lean_dec_ref(v_opt_3608_);
lean_dec_ref(v_opts_3607_);
v_r_3610_ = lean_box(v_res_3609_);
return v_r_3610_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3611_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3614_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(lean_object* v_e_3616_, lean_object* v_k_3617_, uint8_t v_cleanupAnnotations_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___f_3624_; uint8_t v___x_3625_; uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___f_3624_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3624_, 0, v_k_3617_);
v___x_3625_ = 1;
v___x_3626_ = 0;
v___x_3627_ = lean_box(0);
v___x_3628_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3616_, v___x_3625_, v___x_3626_, v___x_3625_, v___x_3626_, v___x_3627_, v___f_3624_, v_cleanupAnnotations_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3628_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3628_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
v_a_3637_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3628_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3628_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg___boxed(lean_object* v_e_3645_, lean_object* v_k_3646_, lean_object* v_cleanupAnnotations_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3653_; lean_object* v_res_3654_; 
v_cleanupAnnotations_boxed_3653_ = lean_unbox(v_cleanupAnnotations_3647_);
v_res_3654_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3645_, v_k_3646_, v_cleanupAnnotations_boxed_3653_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_00_u03b1_3655_, lean_object* v_e_3656_, lean_object* v_k_3657_, uint8_t v_cleanupAnnotations_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3656_, v_k_3657_, v_cleanupAnnotations_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_00_u03b1_3665_, lean_object* v_e_3666_, lean_object* v_k_3667_, lean_object* v_cleanupAnnotations_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3674_; lean_object* v_res_3675_; 
v_cleanupAnnotations_boxed_3674_ = lean_unbox(v_cleanupAnnotations_3668_);
v_res_3675_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(v_00_u03b1_3665_, v_e_3666_, v_k_3667_, v_cleanupAnnotations_boxed_3674_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3676_, lean_object* v_x_3677_, lean_object* v_x_3678_){
_start:
{
if (lean_obj_tag(v_x_3676_) == 5)
{
lean_object* v_fn_3683_; lean_object* v_arg_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_fn_3683_ = lean_ctor_get(v_x_3676_, 0);
lean_inc_ref(v_fn_3683_);
v_arg_3684_ = lean_ctor_get(v_x_3676_, 1);
lean_inc_ref(v_arg_3684_);
lean_dec_ref_known(v_x_3676_, 2);
v___x_3685_ = lean_array_set(v_x_3677_, v_x_3678_, v_arg_3684_);
v___x_3686_ = lean_unsigned_to_nat(1u);
v___x_3687_ = lean_nat_sub(v_x_3678_, v___x_3686_);
lean_dec(v_x_3678_);
v_x_3676_ = v_fn_3683_;
v_x_3677_ = v___x_3685_;
v_x_3678_ = v___x_3687_;
goto _start;
}
else
{
lean_object* v___x_3689_; uint8_t v___x_3690_; 
lean_dec(v_x_3678_);
v___x_3689_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3690_ = l_Lean_Expr_isConstOf(v_x_3676_, v___x_3689_);
lean_dec_ref(v_x_3676_);
if (v___x_3690_ == 0)
{
lean_dec_ref(v_x_3677_);
goto v___jp_3680_;
}
else
{
lean_object* v___x_3691_; lean_object* v___x_3692_; uint8_t v___x_3693_; 
v___x_3691_ = lean_unsigned_to_nat(2u);
v___x_3692_ = lean_array_get_size(v_x_3677_);
v___x_3693_ = lean_nat_dec_le(v___x_3691_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_dec_ref(v_x_3677_);
goto v___jp_3680_;
}
else
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3694_ = lean_unsigned_to_nat(1u);
v___x_3695_ = lean_array_fget(v_x_3677_, v___x_3694_);
v___x_3696_ = l_Array_toSubarray___redArg(v_x_3677_, v___x_3691_, v___x_3692_);
v___x_3697_ = l_Subarray_copy___redArg(v___x_3696_);
v___x_3698_ = l_Lean_mkAppN(v___x_3695_, v___x_3697_);
lean_dec_ref(v___x_3697_);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
v___x_3700_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
}
}
v___jp_3680_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
return v___x_3682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3702_, lean_object* v_x_3703_, lean_object* v_x_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v_res_3706_; 
v_res_3706_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3702_, v_x_3703_, v_x_3704_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(lean_object* v_e_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v_dummy_3713_; lean_object* v_nargs_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_dummy_3713_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3714_ = l_Lean_Expr_getAppNumArgs(v_e_3707_);
lean_inc(v_nargs_3714_);
v___x_3715_ = lean_mk_array(v_nargs_3714_, v_dummy_3713_);
v___x_3716_ = lean_unsigned_to_nat(1u);
v___x_3717_ = lean_nat_sub(v_nargs_3714_, v___x_3716_);
lean_dec(v_nargs_3714_);
v___x_3718_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3707_, v___x_3715_, v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v_e_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v_res_3725_; 
v_res_3725_ = l_Lean_Elab_WF_preprocess___lam__0(v_e_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(lean_object* v_ref_3726_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v_ref_3726_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_ref_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v_res_3733_; 
v_res_3733_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3731_);
return v_res_3733_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; 
v___x_3734_ = lean_box(0);
v___x_3735_ = l_Lean_interruptExceptionId;
v___x_3736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v___x_3734_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg(){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0);
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(lean_object* v_x_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___y_3750_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; uint8_t v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; uint8_t v___y_3776_; lean_object* v_fileName_3782_; lean_object* v_fileMap_3783_; lean_object* v_options_3784_; lean_object* v_currRecDepth_3785_; lean_object* v_maxRecDepth_3786_; lean_object* v_ref_3787_; lean_object* v_currNamespace_3788_; lean_object* v_openDecls_3789_; lean_object* v_initHeartbeats_3790_; lean_object* v_maxHeartbeats_3791_; lean_object* v_quotContext_3792_; lean_object* v_currMacroScope_3793_; uint8_t v_diag_3794_; lean_object* v_cancelTk_x3f_3795_; uint8_t v_suppressElabErrors_3796_; lean_object* v_inheritedTraceOptions_3797_; 
v_fileName_3782_ = lean_ctor_get(v___y_3746_, 0);
v_fileMap_3783_ = lean_ctor_get(v___y_3746_, 1);
v_options_3784_ = lean_ctor_get(v___y_3746_, 2);
v_currRecDepth_3785_ = lean_ctor_get(v___y_3746_, 3);
v_maxRecDepth_3786_ = lean_ctor_get(v___y_3746_, 4);
v_ref_3787_ = lean_ctor_get(v___y_3746_, 5);
v_currNamespace_3788_ = lean_ctor_get(v___y_3746_, 6);
v_openDecls_3789_ = lean_ctor_get(v___y_3746_, 7);
v_initHeartbeats_3790_ = lean_ctor_get(v___y_3746_, 8);
v_maxHeartbeats_3791_ = lean_ctor_get(v___y_3746_, 9);
v_quotContext_3792_ = lean_ctor_get(v___y_3746_, 10);
v_currMacroScope_3793_ = lean_ctor_get(v___y_3746_, 11);
v_diag_3794_ = lean_ctor_get_uint8(v___y_3746_, sizeof(void*)*14);
v_cancelTk_x3f_3795_ = lean_ctor_get(v___y_3746_, 12);
v_suppressElabErrors_3796_ = lean_ctor_get_uint8(v___y_3746_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3797_ = lean_ctor_get(v___y_3746_, 13);
if (lean_obj_tag(v_cancelTk_x3f_3795_) == 1)
{
lean_object* v_val_3803_; uint8_t v___x_3804_; 
v_val_3803_ = lean_ctor_get(v_cancelTk_x3f_3795_, 0);
v___x_3804_ = l_IO_CancelToken_isSet(v_val_3803_);
if (v___x_3804_ == 0)
{
goto v___jp_3798_;
}
else
{
lean_object* v___x_3805_; lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
lean_dec_ref(v_x_3742_);
v___x_3805_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
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
else
{
goto v___jp_3798_;
}
v___jp_3749_:
{
if (lean_obj_tag(v___y_3750_) == 0)
{
return v___y_3750_;
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
v_a_3751_ = lean_ctor_get(v___y_3750_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___y_3750_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___y_3750_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___y_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
v___jp_3759_:
{
if (v___y_3776_ == 0)
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3777_ = lean_unsigned_to_nat(1u);
v___x_3778_ = lean_nat_add(v___y_3760_, v___x_3777_);
lean_inc_ref(v___y_3767_);
lean_inc(v___y_3772_);
lean_inc(v___y_3762_);
lean_inc(v___y_3761_);
lean_inc(v___y_3770_);
lean_inc(v___y_3766_);
lean_inc(v___y_3773_);
lean_inc(v___y_3769_);
lean_inc(v___y_3768_);
lean_inc(v___y_3764_);
lean_inc_ref(v___y_3771_);
lean_inc_ref(v___y_3775_);
lean_inc_ref(v___y_3774_);
v___x_3779_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3779_, 0, v___y_3774_);
lean_ctor_set(v___x_3779_, 1, v___y_3775_);
lean_ctor_set(v___x_3779_, 2, v___y_3771_);
lean_ctor_set(v___x_3779_, 3, v___x_3778_);
lean_ctor_set(v___x_3779_, 4, v___y_3764_);
lean_ctor_set(v___x_3779_, 5, v___y_3768_);
lean_ctor_set(v___x_3779_, 6, v___y_3769_);
lean_ctor_set(v___x_3779_, 7, v___y_3773_);
lean_ctor_set(v___x_3779_, 8, v___y_3766_);
lean_ctor_set(v___x_3779_, 9, v___y_3770_);
lean_ctor_set(v___x_3779_, 10, v___y_3761_);
lean_ctor_set(v___x_3779_, 11, v___y_3762_);
lean_ctor_set(v___x_3779_, 12, v___y_3772_);
lean_ctor_set(v___x_3779_, 13, v___y_3767_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*14, v___y_3765_);
lean_ctor_set_uint8(v___x_3779_, sizeof(void*)*14 + 1, v___y_3763_);
lean_inc(v___y_3747_);
lean_inc(v___y_3745_);
lean_inc_ref(v___y_3744_);
lean_inc(v___y_3743_);
v___x_3780_ = lean_apply_6(v_x_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___x_3779_, v___y_3747_, lean_box(0));
v___y_3750_ = v___x_3780_;
goto v___jp_3749_;
}
else
{
lean_object* v___x_3781_; 
lean_dec_ref(v_x_3742_);
lean_inc(v___y_3768_);
v___x_3781_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v___y_3768_);
v___y_3750_ = v___x_3781_;
goto v___jp_3749_;
}
}
v___jp_3798_:
{
lean_object* v___x_3799_; uint8_t v___x_3800_; uint8_t v___x_3801_; 
v___x_3799_ = lean_unsigned_to_nat(0u);
v___x_3800_ = lean_nat_dec_eq(v_maxRecDepth_3786_, v___x_3799_);
v___x_3801_ = lean_bool_not(v___x_3800_);
if (v___x_3801_ == 0)
{
v___y_3760_ = v_currRecDepth_3785_;
v___y_3761_ = v_quotContext_3792_;
v___y_3762_ = v_currMacroScope_3793_;
v___y_3763_ = v_suppressElabErrors_3796_;
v___y_3764_ = v_maxRecDepth_3786_;
v___y_3765_ = v_diag_3794_;
v___y_3766_ = v_initHeartbeats_3790_;
v___y_3767_ = v_inheritedTraceOptions_3797_;
v___y_3768_ = v_ref_3787_;
v___y_3769_ = v_currNamespace_3788_;
v___y_3770_ = v_maxHeartbeats_3791_;
v___y_3771_ = v_options_3784_;
v___y_3772_ = v_cancelTk_x3f_3795_;
v___y_3773_ = v_openDecls_3789_;
v___y_3774_ = v_fileName_3782_;
v___y_3775_ = v_fileMap_3783_;
v___y_3776_ = v___x_3801_;
goto v___jp_3759_;
}
else
{
uint8_t v___x_3802_; 
v___x_3802_ = lean_nat_dec_eq(v_currRecDepth_3785_, v_maxRecDepth_3786_);
v___y_3760_ = v_currRecDepth_3785_;
v___y_3761_ = v_quotContext_3792_;
v___y_3762_ = v_currMacroScope_3793_;
v___y_3763_ = v_suppressElabErrors_3796_;
v___y_3764_ = v_maxRecDepth_3786_;
v___y_3765_ = v_diag_3794_;
v___y_3766_ = v_initHeartbeats_3790_;
v___y_3767_ = v_inheritedTraceOptions_3797_;
v___y_3768_ = v_ref_3787_;
v___y_3769_ = v_currNamespace_3788_;
v___y_3770_ = v_maxHeartbeats_3791_;
v___y_3771_ = v_options_3784_;
v___y_3772_ = v_cancelTk_x3f_3795_;
v___y_3773_ = v_openDecls_3789_;
v___y_3774_ = v_fileName_3782_;
v___y_3775_ = v_fileMap_3783_;
v___y_3776_ = v___x_3802_;
goto v___jp_3759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg___boxed(lean_object* v_x_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec(v___y_3815_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(lean_object* v_pre_3822_, lean_object* v_post_3823_, size_t v_sz_3824_, size_t v_i_3825_, lean_object* v_bs_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
uint8_t v___x_3833_; 
v___x_3833_ = lean_usize_dec_lt(v_i_3825_, v_sz_3824_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; 
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3822_);
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v_bs_3826_);
return v___x_3834_;
}
else
{
lean_object* v_v_3835_; lean_object* v___x_3836_; 
v_v_3835_ = lean_array_uget_borrowed(v_bs_3826_, v_i_3825_);
lean_inc(v_v_3835_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3822_);
v___x_3836_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3822_, v_post_3823_, v_v_3835_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; lean_object* v_bs_x27_3839_; size_t v___x_3840_; size_t v___x_3841_; lean_object* v___x_3842_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___x_3836_, 1);
v___x_3838_ = lean_unsigned_to_nat(0u);
v_bs_x27_3839_ = lean_array_uset(v_bs_3826_, v_i_3825_, v___x_3838_);
v___x_3840_ = ((size_t)1ULL);
v___x_3841_ = lean_usize_add(v_i_3825_, v___x_3840_);
v___x_3842_ = lean_array_uset(v_bs_x27_3839_, v_i_3825_, v_a_3837_);
v_i_3825_ = v___x_3841_;
v_bs_3826_ = v___x_3842_;
goto _start;
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v_bs_3826_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3822_);
v_a_3844_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3836_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3836_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_3852_, lean_object* v_post_3853_, lean_object* v_x_3854_, lean_object* v_x_3855_, lean_object* v_x_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
if (lean_obj_tag(v_x_3854_) == 5)
{
lean_object* v_fn_3863_; lean_object* v_arg_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
v_fn_3863_ = lean_ctor_get(v_x_3854_, 0);
lean_inc_ref(v_fn_3863_);
v_arg_3864_ = lean_ctor_get(v_x_3854_, 1);
lean_inc_ref(v_arg_3864_);
lean_dec_ref_known(v_x_3854_, 2);
v___x_3865_ = lean_array_set(v_x_3855_, v_x_3856_, v_arg_3864_);
v___x_3866_ = lean_unsigned_to_nat(1u);
v___x_3867_ = lean_nat_sub(v_x_3856_, v___x_3866_);
lean_dec(v_x_3856_);
v_x_3854_ = v_fn_3863_;
v_x_3855_ = v___x_3865_;
v_x_3856_ = v___x_3867_;
goto _start;
}
else
{
lean_object* v___x_3869_; 
lean_dec(v_x_3856_);
lean_inc_ref(v_post_3853_);
lean_inc_ref(v_pre_3852_);
v___x_3869_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3852_, v_post_3853_, v_x_3854_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; size_t v_sz_3871_; size_t v___x_3872_; lean_object* v___x_3873_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v_sz_3871_ = lean_array_size(v_x_3855_);
v___x_3872_ = ((size_t)0ULL);
lean_inc_ref(v_post_3853_);
lean_inc_ref(v_pre_3852_);
v___x_3873_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_3852_, v_post_3853_, v_sz_3871_, v___x_3872_, v_x_3855_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___x_3875_ = l_Lean_mkAppN(v_a_3870_, v_a_3874_);
lean_dec(v_a_3874_);
v___x_3876_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3852_, v_post_3853_, v___x_3875_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
return v___x_3876_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec(v_a_3870_);
lean_dec_ref(v_post_3853_);
lean_dec_ref(v_pre_3852_);
v_a_3877_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3873_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3873_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_dec_ref(v_x_3855_);
lean_dec_ref(v_post_3853_);
lean_dec_ref(v_pre_3852_);
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v___x_3885_, lean_object* v_pre_3886_, lean_object* v_e_3887_, lean_object* v_post_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; uint8_t v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; uint8_t v___y_3903_; lean_object* v___y_3913_; uint8_t v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; uint8_t v___y_3918_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; uint8_t v___y_3929_; lean_object* v___y_3930_; uint8_t v___y_3931_; lean_object* v___x_3938_; 
v___x_3938_ = l_Lean_Core_checkSystem(v___x_3885_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v___x_3939_; 
lean_dec_ref_known(v___x_3938_, 1);
lean_inc_ref(v_pre_3886_);
lean_inc(v___y_3893_);
lean_inc_ref(v___y_3892_);
lean_inc(v___y_3891_);
lean_inc_ref(v___y_3890_);
lean_inc_ref(v_e_3887_);
v___x_3939_ = lean_apply_6(v_pre_3886_, v_e_3887_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, lean_box(0));
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_4029_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_4029_ == 0)
{
v___x_3942_ = v___x_3939_;
v_isShared_3943_ = v_isSharedCheck_4029_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3939_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_4029_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___y_3945_; 
switch(lean_obj_tag(v_a_3940_))
{
case 0:
{
lean_object* v_e_4019_; lean_object* v___x_4021_; 
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_e_3887_);
lean_dec_ref(v_pre_3886_);
v_e_4019_ = lean_ctor_get(v_a_3940_, 0);
lean_inc_ref(v_e_4019_);
lean_dec_ref_known(v_a_3940_, 1);
if (v_isShared_3943_ == 0)
{
lean_ctor_set(v___x_3942_, 0, v_e_4019_);
v___x_4021_ = v___x_3942_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_e_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
case 1:
{
lean_object* v_e_4023_; lean_object* v___x_4024_; 
lean_del_object(v___x_3942_);
lean_dec_ref(v_e_3887_);
v_e_4023_ = lean_ctor_get(v_a_3940_, 0);
lean_inc_ref(v_e_4023_);
lean_dec_ref_known(v_a_3940_, 1);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_4024_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_e_4023_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4026_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v___x_4026_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v_a_4025_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4026_;
}
else
{
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_4024_;
}
}
default: 
{
lean_object* v_e_x3f_4027_; 
lean_del_object(v___x_3942_);
v_e_x3f_4027_ = lean_ctor_get(v_a_3940_, 0);
lean_inc(v_e_x3f_4027_);
lean_dec_ref_known(v_a_3940_, 1);
if (lean_obj_tag(v_e_x3f_4027_) == 0)
{
v___y_3945_ = v_e_3887_;
goto v___jp_3944_;
}
else
{
lean_object* v_val_4028_; 
lean_dec_ref(v_e_3887_);
v_val_4028_ = lean_ctor_get(v_e_x3f_4027_, 0);
lean_inc(v_val_4028_);
lean_dec_ref_known(v_e_x3f_4027_, 1);
v___y_3945_ = v_val_4028_;
goto v___jp_3944_;
}
}
}
v___jp_3944_:
{
switch(lean_obj_tag(v___y_3945_))
{
case 7:
{
lean_object* v_binderName_3946_; lean_object* v_binderType_3947_; lean_object* v_body_3948_; uint8_t v_binderInfo_3949_; lean_object* v___x_3950_; 
v_binderName_3946_ = lean_ctor_get(v___y_3945_, 0);
lean_inc(v_binderName_3946_);
v_binderType_3947_ = lean_ctor_get(v___y_3945_, 1);
v_body_3948_ = lean_ctor_get(v___y_3945_, 2);
v_binderInfo_3949_ = lean_ctor_get_uint8(v___y_3945_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3947_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3950_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_binderType_3947_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3950_) == 0)
{
lean_object* v_a_3951_; lean_object* v___x_3952_; 
v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
lean_inc(v_a_3951_);
lean_dec_ref_known(v___x_3950_, 1);
lean_inc_ref(v_body_3948_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3952_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_body_3948_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; size_t v___x_3954_; size_t v___x_3955_; uint8_t v___x_3956_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = lean_ptr_addr(v_binderType_3947_);
v___x_3955_ = lean_ptr_addr(v_a_3951_);
v___x_3956_ = lean_usize_dec_eq(v___x_3954_, v___x_3955_);
if (v___x_3956_ == 0)
{
v___y_3926_ = v_binderName_3946_;
v___y_3927_ = v___y_3945_;
v___y_3928_ = v_a_3951_;
v___y_3929_ = v_binderInfo_3949_;
v___y_3930_ = v_a_3953_;
v___y_3931_ = v___x_3956_;
goto v___jp_3925_;
}
else
{
size_t v___x_3957_; size_t v___x_3958_; uint8_t v___x_3959_; 
v___x_3957_ = lean_ptr_addr(v_body_3948_);
v___x_3958_ = lean_ptr_addr(v_a_3953_);
v___x_3959_ = lean_usize_dec_eq(v___x_3957_, v___x_3958_);
v___y_3926_ = v_binderName_3946_;
v___y_3927_ = v___y_3945_;
v___y_3928_ = v_a_3951_;
v___y_3929_ = v_binderInfo_3949_;
v___y_3930_ = v_a_3953_;
v___y_3931_ = v___x_3959_;
goto v___jp_3925_;
}
}
else
{
lean_dec(v_a_3951_);
lean_dec_ref_known(v___y_3945_, 3);
lean_dec(v_binderName_3946_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3952_;
}
}
else
{
lean_dec(v_binderName_3946_);
lean_dec_ref_known(v___y_3945_, 3);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3950_;
}
}
case 6:
{
lean_object* v_binderName_3960_; lean_object* v_binderType_3961_; lean_object* v_body_3962_; uint8_t v_binderInfo_3963_; lean_object* v___x_3964_; 
v_binderName_3960_ = lean_ctor_get(v___y_3945_, 0);
lean_inc(v_binderName_3960_);
v_binderType_3961_ = lean_ctor_get(v___y_3945_, 1);
v_body_3962_ = lean_ctor_get(v___y_3945_, 2);
v_binderInfo_3963_ = lean_ctor_get_uint8(v___y_3945_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3961_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3964_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_binderType_3961_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
lean_inc_ref(v_body_3962_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3966_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_body_3962_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; size_t v___x_3968_; size_t v___x_3969_; uint8_t v___x_3970_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = lean_ptr_addr(v_binderType_3961_);
v___x_3969_ = lean_ptr_addr(v_a_3965_);
v___x_3970_ = lean_usize_dec_eq(v___x_3968_, v___x_3969_);
if (v___x_3970_ == 0)
{
v___y_3913_ = v___y_3945_;
v___y_3914_ = v_binderInfo_3963_;
v___y_3915_ = v_binderName_3960_;
v___y_3916_ = v_a_3967_;
v___y_3917_ = v_a_3965_;
v___y_3918_ = v___x_3970_;
goto v___jp_3912_;
}
else
{
size_t v___x_3971_; size_t v___x_3972_; uint8_t v___x_3973_; 
v___x_3971_ = lean_ptr_addr(v_body_3962_);
v___x_3972_ = lean_ptr_addr(v_a_3967_);
v___x_3973_ = lean_usize_dec_eq(v___x_3971_, v___x_3972_);
v___y_3913_ = v___y_3945_;
v___y_3914_ = v_binderInfo_3963_;
v___y_3915_ = v_binderName_3960_;
v___y_3916_ = v_a_3967_;
v___y_3917_ = v_a_3965_;
v___y_3918_ = v___x_3973_;
goto v___jp_3912_;
}
}
else
{
lean_dec(v_a_3965_);
lean_dec(v_binderName_3960_);
lean_dec_ref_known(v___y_3945_, 3);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3966_;
}
}
else
{
lean_dec(v_binderName_3960_);
lean_dec_ref_known(v___y_3945_, 3);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3964_;
}
}
case 8:
{
lean_object* v_declName_3974_; lean_object* v_type_3975_; lean_object* v_value_3976_; lean_object* v_body_3977_; uint8_t v_nondep_3978_; lean_object* v___x_3979_; 
v_declName_3974_ = lean_ctor_get(v___y_3945_, 0);
lean_inc(v_declName_3974_);
v_type_3975_ = lean_ctor_get(v___y_3945_, 1);
v_value_3976_ = lean_ctor_get(v___y_3945_, 2);
v_body_3977_ = lean_ctor_get(v___y_3945_, 3);
lean_inc_ref(v_body_3977_);
v_nondep_3978_ = lean_ctor_get_uint8(v___y_3945_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3975_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3979_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_type_3975_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref_known(v___x_3979_, 1);
lean_inc_ref(v_value_3976_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3981_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_value_3976_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
lean_inc_ref(v_body_3977_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3983_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_body_3977_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; size_t v___x_3985_; size_t v___x_3986_; uint8_t v___x_3987_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_a_3984_);
lean_dec_ref_known(v___x_3983_, 1);
v___x_3985_ = lean_ptr_addr(v_type_3975_);
v___x_3986_ = lean_ptr_addr(v_a_3980_);
v___x_3987_ = lean_usize_dec_eq(v___x_3985_, v___x_3986_);
if (v___x_3987_ == 0)
{
v___y_3896_ = v_a_3980_;
v___y_3897_ = v_a_3982_;
v___y_3898_ = v_body_3977_;
v___y_3899_ = v___y_3945_;
v___y_3900_ = v_nondep_3978_;
v___y_3901_ = v_a_3984_;
v___y_3902_ = v_declName_3974_;
v___y_3903_ = v___x_3987_;
goto v___jp_3895_;
}
else
{
size_t v___x_3988_; size_t v___x_3989_; uint8_t v___x_3990_; 
v___x_3988_ = lean_ptr_addr(v_value_3976_);
v___x_3989_ = lean_ptr_addr(v_a_3982_);
v___x_3990_ = lean_usize_dec_eq(v___x_3988_, v___x_3989_);
v___y_3896_ = v_a_3980_;
v___y_3897_ = v_a_3982_;
v___y_3898_ = v_body_3977_;
v___y_3899_ = v___y_3945_;
v___y_3900_ = v_nondep_3978_;
v___y_3901_ = v_a_3984_;
v___y_3902_ = v_declName_3974_;
v___y_3903_ = v___x_3990_;
goto v___jp_3895_;
}
}
else
{
lean_dec(v_a_3982_);
lean_dec(v_a_3980_);
lean_dec_ref(v_body_3977_);
lean_dec_ref_known(v___y_3945_, 4);
lean_dec(v_declName_3974_);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3983_;
}
}
else
{
lean_dec(v_a_3980_);
lean_dec_ref(v_body_3977_);
lean_dec(v_declName_3974_);
lean_dec_ref_known(v___y_3945_, 4);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3981_;
}
}
else
{
lean_dec_ref(v_body_3977_);
lean_dec(v_declName_3974_);
lean_dec_ref_known(v___y_3945_, 4);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3979_;
}
}
case 5:
{
lean_object* v_dummy_3991_; lean_object* v_nargs_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; 
v_dummy_3991_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3992_ = l_Lean_Expr_getAppNumArgs(v___y_3945_);
lean_inc(v_nargs_3992_);
v___x_3993_ = lean_mk_array(v_nargs_3992_, v_dummy_3991_);
v___x_3994_ = lean_unsigned_to_nat(1u);
v___x_3995_ = lean_nat_sub(v_nargs_3992_, v___x_3994_);
lean_dec(v_nargs_3992_);
v___x_3996_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3886_, v_post_3888_, v___y_3945_, v___x_3993_, v___x_3995_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3996_;
}
case 10:
{
lean_object* v_data_3997_; lean_object* v_expr_3998_; lean_object* v___x_3999_; 
v_data_3997_ = lean_ctor_get(v___y_3945_, 0);
v_expr_3998_ = lean_ctor_get(v___y_3945_, 1);
lean_inc_ref(v_expr_3998_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_3999_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_expr_3998_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; size_t v___x_4001_; size_t v___x_4002_; uint8_t v___x_4003_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref_known(v___x_3999_, 1);
v___x_4001_ = lean_ptr_addr(v_expr_3998_);
v___x_4002_ = lean_ptr_addr(v_a_4000_);
v___x_4003_ = lean_usize_dec_eq(v___x_4001_, v___x_4002_);
if (v___x_4003_ == 0)
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
lean_inc(v_data_3997_);
lean_dec_ref_known(v___y_3945_, 2);
v___x_4004_ = l_Lean_Expr_mdata___override(v_data_3997_, v_a_4000_);
v___x_4005_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_4004_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4005_;
}
else
{
lean_object* v___x_4006_; 
lean_dec(v_a_4000_);
v___x_4006_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___y_3945_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4006_;
}
}
else
{
lean_dec_ref_known(v___y_3945_, 2);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_3999_;
}
}
case 11:
{
lean_object* v_typeName_4007_; lean_object* v_idx_4008_; lean_object* v_struct_4009_; lean_object* v___x_4010_; 
v_typeName_4007_ = lean_ctor_get(v___y_3945_, 0);
v_idx_4008_ = lean_ctor_get(v___y_3945_, 1);
v_struct_4009_ = lean_ctor_get(v___y_3945_, 2);
lean_inc_ref(v_struct_4009_);
lean_inc_ref(v_post_3888_);
lean_inc_ref(v_pre_3886_);
v___x_4010_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3886_, v_post_3888_, v_struct_4009_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; size_t v___x_4012_; size_t v___x_4013_; uint8_t v___x_4014_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = lean_ptr_addr(v_struct_4009_);
v___x_4013_ = lean_ptr_addr(v_a_4011_);
v___x_4014_ = lean_usize_dec_eq(v___x_4012_, v___x_4013_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_inc(v_idx_4008_);
lean_inc(v_typeName_4007_);
lean_dec_ref_known(v___y_3945_, 3);
v___x_4015_ = l_Lean_Expr_proj___override(v_typeName_4007_, v_idx_4008_, v_a_4011_);
v___x_4016_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_4015_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4016_;
}
else
{
lean_object* v___x_4017_; 
lean_dec(v_a_4011_);
v___x_4017_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___y_3945_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4017_;
}
}
else
{
lean_dec_ref_known(v___y_3945_, 3);
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_pre_3886_);
return v___x_4010_;
}
}
default: 
{
lean_object* v___x_4018_; 
v___x_4018_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___y_3945_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_4018_;
}
}
}
}
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_e_3887_);
lean_dec_ref(v_pre_3886_);
v_a_4030_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_3939_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_3939_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec_ref(v_post_3888_);
lean_dec_ref(v_e_3887_);
lean_dec_ref(v_pre_3886_);
v_a_4038_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_3938_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_3938_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
v___jp_3895_:
{
if (v___y_3903_ == 0)
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_dec_ref(v___y_3899_);
lean_dec_ref(v___y_3898_);
v___x_3904_ = l_Lean_Expr_letE___override(v___y_3902_, v___y_3896_, v___y_3897_, v___y_3901_, v___y_3900_);
v___x_3905_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_3904_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3905_;
}
else
{
size_t v___x_3906_; size_t v___x_3907_; uint8_t v___x_3908_; 
v___x_3906_ = lean_ptr_addr(v___y_3898_);
lean_dec_ref(v___y_3898_);
v___x_3907_ = lean_ptr_addr(v___y_3901_);
v___x_3908_ = lean_usize_dec_eq(v___x_3906_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec_ref(v___y_3899_);
v___x_3909_ = l_Lean_Expr_letE___override(v___y_3902_, v___y_3896_, v___y_3897_, v___y_3901_, v___y_3900_);
v___x_3910_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_3909_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; 
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v___y_3896_);
v___x_3911_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___y_3899_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3911_;
}
}
}
v___jp_3912_:
{
if (v___y_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
lean_dec_ref(v___y_3913_);
v___x_3919_ = l_Lean_Expr_lam___override(v___y_3915_, v___y_3917_, v___y_3916_, v___y_3914_);
v___x_3920_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_3919_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3920_;
}
else
{
uint8_t v___x_3921_; 
v___x_3921_ = l_Lean_instBEqBinderInfo_beq(v___y_3914_, v___y_3914_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_dec_ref(v___y_3913_);
v___x_3922_ = l_Lean_Expr_lam___override(v___y_3915_, v___y_3917_, v___y_3916_, v___y_3914_);
v___x_3923_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_3922_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3923_;
}
else
{
lean_object* v___x_3924_; 
lean_dec_ref(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
v___x_3924_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___y_3913_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3924_;
}
}
}
v___jp_3925_:
{
if (v___y_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec_ref(v___y_3927_);
v___x_3932_ = l_Lean_Expr_forallE___override(v___y_3926_, v___y_3928_, v___y_3930_, v___y_3929_);
v___x_3933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_3932_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3933_;
}
else
{
uint8_t v___x_3934_; 
v___x_3934_ = l_Lean_instBEqBinderInfo_beq(v___y_3929_, v___y_3929_);
if (v___x_3934_ == 0)
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
lean_dec_ref(v___y_3927_);
v___x_3935_ = l_Lean_Expr_forallE___override(v___y_3926_, v___y_3928_, v___y_3930_, v___y_3929_);
v___x_3936_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___x_3935_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3936_;
}
else
{
lean_object* v___x_3937_; 
lean_dec_ref(v___y_3930_);
lean_dec_ref(v___y_3928_);
lean_dec(v___y_3926_);
v___x_3937_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3886_, v_post_3888_, v___y_3927_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v___x_3937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v___x_4046_, lean_object* v_pre_4047_, lean_object* v_e_4048_, lean_object* v_post_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v___x_4046_, v_pre_4047_, v_e_4048_, v_post_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_4057_, lean_object* v_post_4058_, lean_object* v_e_4059_, lean_object* v_a_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
lean_inc(v_a_4060_);
v___x_4066_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4066_, 0, lean_box(0));
lean_closure_set(v___x_4066_, 1, lean_box(0));
lean_closure_set(v___x_4066_, 2, v_a_4060_);
v___x_4067_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_4066_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4099_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4070_ = v___x_4067_;
v_isShared_4071_ = v_isSharedCheck_4099_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4067_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4099_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4072_; 
v___x_4072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_4068_, v_e_4059_);
lean_dec(v_a_4068_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v___x_4073_; lean_object* v___f_4074_; lean_object* v___x_4075_; 
lean_del_object(v___x_4070_);
v___x_4073_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
lean_inc_ref(v_e_4059_);
v___f_4074_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4074_, 0, v___x_4073_);
lean_closure_set(v___f_4074_, 1, v_pre_4057_);
lean_closure_set(v___f_4074_, 2, v_e_4059_);
lean_closure_set(v___f_4074_, 3, v_post_4058_);
v___x_4075_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v___f_4074_, v_a_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v_a_4076_; lean_object* v___f_4077_; lean_object* v___x_4078_; 
v_a_4076_ = lean_ctor_get(v___x_4075_, 0);
lean_inc_n(v_a_4076_, 2);
lean_dec_ref_known(v___x_4075_, 1);
lean_inc(v_a_4060_);
v___f_4077_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4077_, 0, v_a_4060_);
lean_closure_set(v___f_4077_, 1, v_e_4059_);
lean_closure_set(v___f_4077_, 2, v_a_4076_);
v___x_4078_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_4077_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4085_ == 0)
{
lean_object* v_unused_4086_; 
v_unused_4086_ = lean_ctor_get(v___x_4078_, 0);
lean_dec(v_unused_4086_);
v___x_4080_ = v___x_4078_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_dec(v___x_4078_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
lean_ctor_set(v___x_4080_, 0, v_a_4076_);
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4076_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec(v_a_4076_);
v_a_4087_ = lean_ctor_get(v___x_4078_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4078_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4078_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4078_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
else
{
lean_dec_ref(v_e_4059_);
return v___x_4075_;
}
}
else
{
lean_object* v_val_4095_; lean_object* v___x_4097_; 
lean_dec_ref(v_e_4059_);
lean_dec_ref(v_post_4058_);
lean_dec_ref(v_pre_4057_);
v_val_4095_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_val_4095_);
lean_dec_ref_known(v___x_4072_, 1);
if (v_isShared_4071_ == 0)
{
lean_ctor_set(v___x_4070_, 0, v_val_4095_);
v___x_4097_ = v___x_4070_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_val_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec_ref(v_e_4059_);
lean_dec_ref(v_post_4058_);
lean_dec_ref(v_pre_4057_);
v_a_4100_ = lean_ctor_get(v___x_4067_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4067_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4067_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4067_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_4108_, lean_object* v_post_4109_, lean_object* v_e_4110_, lean_object* v_a_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; 
lean_inc_ref(v_post_4109_);
lean_inc(v___y_4115_);
lean_inc_ref(v___y_4114_);
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
lean_inc_ref(v_e_4110_);
v___x_4117_ = lean_apply_6(v_post_4109_, v_e_4110_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, lean_box(0));
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4136_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4120_ = v___x_4117_;
v_isShared_4121_ = v_isSharedCheck_4136_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4117_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4136_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
switch(lean_obj_tag(v_a_4118_))
{
case 0:
{
lean_object* v_e_4122_; lean_object* v___x_4124_; 
lean_dec_ref(v_e_4110_);
lean_dec_ref(v_post_4109_);
lean_dec_ref(v_pre_4108_);
v_e_4122_ = lean_ctor_get(v_a_4118_, 0);
lean_inc_ref(v_e_4122_);
lean_dec_ref_known(v_a_4118_, 1);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v_e_4122_);
v___x_4124_ = v___x_4120_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_e_4122_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
case 1:
{
lean_object* v_e_4126_; lean_object* v___x_4127_; 
lean_del_object(v___x_4120_);
lean_dec_ref(v_e_4110_);
v_e_4126_ = lean_ctor_get(v_a_4118_, 0);
lean_inc_ref(v_e_4126_);
lean_dec_ref_known(v_a_4118_, 1);
v___x_4127_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4108_, v_post_4109_, v_e_4126_, v_a_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4127_;
}
default: 
{
lean_object* v_e_x3f_4128_; 
lean_dec_ref(v_post_4109_);
lean_dec_ref(v_pre_4108_);
v_e_x3f_4128_ = lean_ctor_get(v_a_4118_, 0);
lean_inc(v_e_x3f_4128_);
lean_dec_ref_known(v_a_4118_, 1);
if (lean_obj_tag(v_e_x3f_4128_) == 0)
{
lean_object* v___x_4130_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v_e_4110_);
v___x_4130_ = v___x_4120_;
goto v_reusejp_4129_;
}
else
{
lean_object* v_reuseFailAlloc_4131_; 
v_reuseFailAlloc_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4131_, 0, v_e_4110_);
v___x_4130_ = v_reuseFailAlloc_4131_;
goto v_reusejp_4129_;
}
v_reusejp_4129_:
{
return v___x_4130_;
}
}
else
{
lean_object* v_val_4132_; lean_object* v___x_4134_; 
lean_dec_ref(v_e_4110_);
v_val_4132_ = lean_ctor_get(v_e_x3f_4128_, 0);
lean_inc(v_val_4132_);
lean_dec_ref_known(v_e_x3f_4128_, 1);
if (v_isShared_4121_ == 0)
{
lean_ctor_set(v___x_4120_, 0, v_val_4132_);
v___x_4134_ = v___x_4120_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_val_4132_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec_ref(v_e_4110_);
lean_dec_ref(v_post_4109_);
lean_dec_ref(v_pre_4108_);
v_a_4137_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4117_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4117_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4145_, lean_object* v_post_4146_, lean_object* v_e_4147_, lean_object* v_a_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4145_, v_post_4146_, v_e_4147_, v_a_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v_a_4148_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6___boxed(lean_object* v_pre_4155_, lean_object* v_post_4156_, lean_object* v_sz_4157_, lean_object* v_i_4158_, lean_object* v_bs_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
size_t v_sz_boxed_4166_; size_t v_i_boxed_4167_; lean_object* v_res_4168_; 
v_sz_boxed_4166_ = lean_unbox_usize(v_sz_4157_);
lean_dec(v_sz_4157_);
v_i_boxed_4167_ = lean_unbox_usize(v_i_4158_);
lean_dec(v_i_4158_);
v_res_4168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_4155_, v_post_4156_, v_sz_boxed_4166_, v_i_boxed_4167_, v_bs_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4169_, lean_object* v_post_4170_, lean_object* v_x_4171_, lean_object* v_x_4172_, lean_object* v_x_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4169_, v_post_4170_, v_x_4171_, v_x_4172_, v_x_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object* v_pre_4181_, lean_object* v_post_4182_, lean_object* v_e_4183_, lean_object* v_a_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4181_, v_post_4182_, v_e_4183_, v_a_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v_a_4184_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object* v_input_4191_, lean_object* v_pre_4192_, lean_object* v_post_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v_a_4201_; lean_object* v___x_4202_; 
v___x_4199_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_4200_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4199_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
lean_inc(v_a_4201_);
lean_dec_ref(v___x_4200_);
v___x_4202_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4192_, v_post_4193_, v_input_4191_, v_a_4201_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___x_4204_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4204_, 0, lean_box(0));
lean_closure_set(v___x_4204_, 1, lean_box(0));
lean_closure_set(v___x_4204_, 2, v_a_4201_);
v___x_4205_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4204_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4212_ == 0)
{
lean_object* v_unused_4213_; 
v_unused_4213_ = lean_ctor_get(v___x_4205_, 0);
lean_dec(v_unused_4213_);
v___x_4207_ = v___x_4205_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_dec(v___x_4205_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v_a_4203_);
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4203_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
else
{
lean_dec(v_a_4201_);
return v___x_4202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object* v_input_4214_, lean_object* v_pre_4215_, lean_object* v_post_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4214_, v_pre_4215_, v_post_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
return v_res_4222_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4223_; double v___x_4224_; 
v___x_4223_ = lean_unsigned_to_nat(0u);
v___x_4224_ = lean_float_of_nat(v___x_4223_);
return v___x_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_4228_, lean_object* v_msg_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_ref_4235_; lean_object* v___x_4236_; lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4281_; 
v_ref_4235_ = lean_ctor_get(v___y_4232_, 5);
v___x_4236_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4239_ = v___x_4236_;
v_isShared_4240_ = v_isSharedCheck_4281_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4236_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4281_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4241_; lean_object* v_traceState_4242_; lean_object* v_env_4243_; lean_object* v_nextMacroScope_4244_; lean_object* v_ngen_4245_; lean_object* v_auxDeclNGen_4246_; lean_object* v_cache_4247_; lean_object* v_messages_4248_; lean_object* v_infoState_4249_; lean_object* v_snapshotTasks_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4280_; 
v___x_4241_ = lean_st_ref_take(v___y_4233_);
v_traceState_4242_ = lean_ctor_get(v___x_4241_, 4);
v_env_4243_ = lean_ctor_get(v___x_4241_, 0);
v_nextMacroScope_4244_ = lean_ctor_get(v___x_4241_, 1);
v_ngen_4245_ = lean_ctor_get(v___x_4241_, 2);
v_auxDeclNGen_4246_ = lean_ctor_get(v___x_4241_, 3);
v_cache_4247_ = lean_ctor_get(v___x_4241_, 5);
v_messages_4248_ = lean_ctor_get(v___x_4241_, 6);
v_infoState_4249_ = lean_ctor_get(v___x_4241_, 7);
v_snapshotTasks_4250_ = lean_ctor_get(v___x_4241_, 8);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4252_ = v___x_4241_;
v_isShared_4253_ = v_isSharedCheck_4280_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_snapshotTasks_4250_);
lean_inc(v_infoState_4249_);
lean_inc(v_messages_4248_);
lean_inc(v_cache_4247_);
lean_inc(v_traceState_4242_);
lean_inc(v_auxDeclNGen_4246_);
lean_inc(v_ngen_4245_);
lean_inc(v_nextMacroScope_4244_);
lean_inc(v_env_4243_);
lean_dec(v___x_4241_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4280_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
uint64_t v_tid_4254_; lean_object* v_traces_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4279_; 
v_tid_4254_ = lean_ctor_get_uint64(v_traceState_4242_, sizeof(void*)*1);
v_traces_4255_ = lean_ctor_get(v_traceState_4242_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v_traceState_4242_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4257_ = v_traceState_4242_;
v_isShared_4258_ = v_isSharedCheck_4279_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_traces_4255_);
lean_dec(v_traceState_4242_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4279_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4259_; double v___x_4260_; uint8_t v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4269_; 
v___x_4259_ = lean_box(0);
v___x_4260_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0);
v___x_4261_ = 0;
v___x_4262_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1));
v___x_4263_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4263_, 0, v_cls_4228_);
lean_ctor_set(v___x_4263_, 1, v___x_4259_);
lean_ctor_set(v___x_4263_, 2, v___x_4262_);
lean_ctor_set_float(v___x_4263_, sizeof(void*)*3, v___x_4260_);
lean_ctor_set_float(v___x_4263_, sizeof(void*)*3 + 8, v___x_4260_);
lean_ctor_set_uint8(v___x_4263_, sizeof(void*)*3 + 16, v___x_4261_);
v___x_4264_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2));
v___x_4265_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v_a_4237_);
lean_ctor_set(v___x_4265_, 2, v___x_4264_);
lean_inc(v_ref_4235_);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v_ref_4235_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = l_Lean_PersistentArray_push___redArg(v_traces_4255_, v___x_4266_);
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v___x_4267_);
v___x_4269_ = v___x_4257_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4267_);
lean_ctor_set_uint64(v_reuseFailAlloc_4278_, sizeof(void*)*1, v_tid_4254_);
v___x_4269_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
lean_object* v___x_4271_; 
if (v_isShared_4253_ == 0)
{
lean_ctor_set(v___x_4252_, 4, v___x_4269_);
v___x_4271_ = v___x_4252_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_env_4243_);
lean_ctor_set(v_reuseFailAlloc_4277_, 1, v_nextMacroScope_4244_);
lean_ctor_set(v_reuseFailAlloc_4277_, 2, v_ngen_4245_);
lean_ctor_set(v_reuseFailAlloc_4277_, 3, v_auxDeclNGen_4246_);
lean_ctor_set(v_reuseFailAlloc_4277_, 4, v___x_4269_);
lean_ctor_set(v_reuseFailAlloc_4277_, 5, v_cache_4247_);
lean_ctor_set(v_reuseFailAlloc_4277_, 6, v_messages_4248_);
lean_ctor_set(v_reuseFailAlloc_4277_, 7, v_infoState_4249_);
lean_ctor_set(v_reuseFailAlloc_4277_, 8, v_snapshotTasks_4250_);
v___x_4271_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4275_; 
v___x_4272_ = lean_st_ref_set(v___y_4233_, v___x_4271_);
v___x_4273_ = lean_box(0);
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4273_);
v___x_4275_ = v___x_4239_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v___x_4273_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_4282_, lean_object* v_msg_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_4282_, v_msg_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4290_, size_t v_i_4291_, lean_object* v_bs_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_){
_start:
{
uint8_t v___x_4298_; 
v___x_4298_ = lean_usize_dec_lt(v_i_4291_, v_sz_4290_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v_bs_4292_);
return v___x_4299_;
}
else
{
lean_object* v_v_4300_; lean_object* v___x_4301_; 
v_v_4300_ = lean_array_uget_borrowed(v_bs_4292_, v_i_4291_);
lean_inc(v_v_4300_);
v___x_4301_ = l_Lean_Elab_WF_mkWfParam(v_v_4300_, v___y_4293_, v___y_4294_, v___y_4295_, v___y_4296_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; lean_object* v_bs_x27_4304_; size_t v___x_4305_; size_t v___x_4306_; lean_object* v___x_4307_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
v___x_4303_ = lean_unsigned_to_nat(0u);
v_bs_x27_4304_ = lean_array_uset(v_bs_4292_, v_i_4291_, v___x_4303_);
v___x_4305_ = ((size_t)1ULL);
v___x_4306_ = lean_usize_add(v_i_4291_, v___x_4305_);
v___x_4307_ = lean_array_uset(v_bs_x27_4304_, v_i_4291_, v_a_4302_);
v_i_4291_ = v___x_4306_;
v_bs_4292_ = v___x_4307_;
goto _start;
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_dec_ref(v_bs_4292_);
v_a_4309_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4301_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4301_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4317_, lean_object* v_i_4318_, lean_object* v_bs_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
size_t v_sz_boxed_4325_; size_t v_i_boxed_4326_; lean_object* v_res_4327_; 
v_sz_boxed_4325_ = lean_unbox_usize(v_sz_4317_);
lean_dec(v_sz_4317_);
v_i_boxed_4326_ = lean_unbox_usize(v_i_4318_);
lean_dec(v_i_4318_);
v_res_4327_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4325_, v_i_boxed_4326_, v_bs_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
return v_res_4327_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_4328_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4329_; 
v___x_4329_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_box(0));
return v___x_4329_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__1, &l_Lean_Elab_WF_preprocess___lam__2___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1);
v___x_4331_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__0, &l_Lean_Elab_WF_preprocess___lam__2___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0);
v___x_4332_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4332_, 0, v___x_4331_);
lean_ctor_set(v___x_4332_, 1, v___x_4331_);
lean_ctor_set(v___x_4332_, 2, v___x_4330_);
lean_ctor_set(v___x_4332_, 3, v___x_4330_);
return v___x_4332_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3(void){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4333_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4(void){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__3, &l_Lean_Elab_WF_preprocess___lam__2___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3);
v___x_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
return v___x_4335_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5(void){
_start:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = lean_unsigned_to_nat(0u);
v___x_4337_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v___x_4337_);
lean_ctor_set(v___x_4338_, 1, v___x_4336_);
return v___x_4338_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6(void){
_start:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4339_ = lean_unsigned_to_nat(32u);
v___x_4340_ = lean_mk_empty_array_with_capacity(v___x_4339_);
v___x_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
return v___x_4341_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7(void){
_start:
{
size_t v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4342_ = ((size_t)5ULL);
v___x_4343_ = lean_unsigned_to_nat(0u);
v___x_4344_ = lean_unsigned_to_nat(32u);
v___x_4345_ = lean_mk_empty_array_with_capacity(v___x_4344_);
v___x_4346_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__6, &l_Lean_Elab_WF_preprocess___lam__2___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6);
v___x_4347_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4347_, 0, v___x_4346_);
lean_ctor_set(v___x_4347_, 1, v___x_4345_);
lean_ctor_set(v___x_4347_, 2, v___x_4343_);
lean_ctor_set(v___x_4347_, 3, v___x_4343_);
lean_ctor_set_usize(v___x_4347_, 4, v___x_4342_);
return v___x_4347_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__8(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4348_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__7, &l_Lean_Elab_WF_preprocess___lam__2___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7);
v___x_4349_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4350_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4350_, 0, v___x_4349_);
lean_ctor_set(v___x_4350_, 1, v___x_4349_);
lean_ctor_set(v___x_4350_, 2, v___x_4349_);
lean_ctor_set(v___x_4350_, 3, v___x_4348_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__9(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4351_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__8, &l_Lean_Elab_WF_preprocess___lam__2___closed__8_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__8);
v___x_4352_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__5, &l_Lean_Elab_WF_preprocess___lam__2___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5);
v___x_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
lean_ctor_set(v___x_4353_, 1, v___x_4351_);
return v___x_4353_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4363_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__13));
v___x_4364_ = l_Lean_Name_append(v___x_4363_, v___x_4362_);
return v___x_4364_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16(void){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__15));
v___x_4367_ = l_Lean_stringToMessageData(v___x_4366_);
return v___x_4367_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4369_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__17));
v___x_4370_ = l_Lean_stringToMessageData(v___x_4369_);
return v___x_4370_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__20(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4372_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__19));
v___x_4373_ = l_Lean_stringToMessageData(v___x_4372_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2(uint8_t v___x_4374_, lean_object* v_a_4375_, lean_object* v___f_4376_, lean_object* v___f_4377_, lean_object* v_xs_4378_, lean_object* v_x_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
size_t v_sz_4385_; size_t v___x_4386_; lean_object* v___x_4387_; 
v_sz_4385_ = lean_array_size(v_xs_4378_);
v___x_4386_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4378_);
v___x_4387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4385_, v___x_4386_, v_xs_4378_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4387_) == 0)
{
lean_object* v_a_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref_known(v___x_4387_, 1);
v___x_4389_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4390_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_4391_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4389_, v___x_4390_, v___x_4374_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; lean_object* v___x_4393_; uint8_t v___x_4394_; lean_object* v___x_4395_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
v___x_4393_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_4394_ = 0;
v___x_4395_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4392_, v___x_4393_, v___x_4394_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v___x_4397_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_4398_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4396_, v___x_4397_, v___x_4374_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4380_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
lean_inc(v_a_4401_);
lean_dec_ref_known(v___x_4400_, 1);
v___x_4402_ = l_Lean_Expr_beta(v_a_4375_, v_a_4388_);
v___x_4403_ = lean_unsigned_to_nat(1u);
v___x_4404_ = lean_mk_empty_array_with_capacity(v___x_4403_);
v___x_4405_ = lean_array_push(v___x_4404_, v_a_4399_);
v___x_4406_ = lean_box(0);
v___x_4407_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__9, &l_Lean_Elab_WF_preprocess___lam__2___closed__9_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__9);
lean_inc_ref(v___x_4402_);
v___x_4408_ = l_Lean_Meta_simp(v___x_4402_, v_a_4401_, v___x_4405_, v___x_4406_, v___x_4407_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_fst_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4478_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v_fst_4410_ = lean_ctor_get(v_a_4409_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_a_4409_);
if (v_isSharedCheck_4478_ == 0)
{
lean_object* v_unused_4479_; 
v_unused_4479_ = lean_ctor_get(v_a_4409_, 1);
lean_dec(v_unused_4479_);
v___x_4412_ = v_a_4409_;
v_isShared_4413_ = v_isSharedCheck_4478_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_fst_4410_);
lean_dec(v_a_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4478_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v_expr_4414_; lean_object* v_proof_x3f_4415_; uint8_t v_cache_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4477_; 
v_expr_4414_ = lean_ctor_get(v_fst_4410_, 0);
v_proof_x3f_4415_ = lean_ctor_get(v_fst_4410_, 1);
v_cache_4416_ = lean_ctor_get_uint8(v_fst_4410_, sizeof(void*)*2);
v_isSharedCheck_4477_ = !lean_is_exclusive(v_fst_4410_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4418_ = v_fst_4410_;
v_isShared_4419_ = v_isSharedCheck_4477_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_proof_x3f_4415_);
lean_inc(v_expr_4414_);
lean_dec(v_fst_4410_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4477_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4420_; 
lean_inc_ref(v_expr_4414_);
v___x_4420_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4414_, v___f_4376_, v___f_4377_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4422_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v___x_4422_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4421_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v_options_4433_; uint8_t v_hasTrace_4434_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4423_);
lean_dec_ref_known(v___x_4422_, 1);
v_options_4433_ = lean_ctor_get(v___y_4382_, 2);
v_hasTrace_4434_ = lean_ctor_get_uint8(v_options_4433_, sizeof(void*)*1);
if (v_hasTrace_4434_ == 0)
{
lean_dec_ref(v_expr_4414_);
lean_del_object(v___x_4412_);
lean_dec_ref(v___x_4402_);
v___y_4425_ = v___y_4380_;
v___y_4426_ = v___y_4381_;
v___y_4427_ = v___y_4382_;
v___y_4428_ = v___y_4383_;
goto v___jp_4424_;
}
else
{
lean_object* v_inheritedTraceOptions_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; uint8_t v___x_4438_; 
v_inheritedTraceOptions_4435_ = lean_ctor_get(v___y_4382_, 13);
v___x_4436_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4437_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__14, &l_Lean_Elab_WF_preprocess___lam__2___closed__14_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14);
v___x_4438_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4435_, v_options_4433_, v___x_4437_);
if (v___x_4438_ == 0)
{
lean_dec_ref(v_expr_4414_);
lean_del_object(v___x_4412_);
lean_dec_ref(v___x_4402_);
v___y_4425_ = v___y_4380_;
v___y_4426_ = v___y_4381_;
v___y_4427_ = v___y_4382_;
v___y_4428_ = v___y_4383_;
goto v___jp_4424_;
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4442_; 
v___x_4439_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__16, &l_Lean_Elab_WF_preprocess___lam__2___closed__16_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16);
v___x_4440_ = l_Lean_indentExpr(v___x_4402_);
if (v_isShared_4413_ == 0)
{
lean_ctor_set_tag(v___x_4412_, 7);
lean_ctor_set(v___x_4412_, 1, v___x_4440_);
lean_ctor_set(v___x_4412_, 0, v___x_4439_);
v___x_4442_ = v___x_4412_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4439_);
lean_ctor_set(v_reuseFailAlloc_4460_, 1, v___x_4440_);
v___x_4442_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4443_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__18, &l_Lean_Elab_WF_preprocess___lam__2___closed__18_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18);
v___x_4444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4442_);
lean_ctor_set(v___x_4444_, 1, v___x_4443_);
v___x_4445_ = l_Lean_indentExpr(v_expr_4414_);
v___x_4446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4444_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
v___x_4447_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__20, &l_Lean_Elab_WF_preprocess___lam__2___closed__20_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__20);
v___x_4448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4446_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
lean_inc(v_a_4423_);
v___x_4449_ = l_Lean_indentExpr(v_a_4423_);
v___x_4450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4450_, 0, v___x_4448_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
v___x_4451_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v___x_4436_, v___x_4450_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_dec_ref_known(v___x_4451_, 1);
v___y_4425_ = v___y_4380_;
v___y_4426_ = v___y_4381_;
v___y_4427_ = v___y_4382_;
v___y_4428_ = v___y_4383_;
goto v___jp_4424_;
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_a_4423_);
lean_del_object(v___x_4418_);
lean_dec(v_proof_x3f_4415_);
lean_dec_ref(v_xs_4378_);
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4451_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4451_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
}
v___jp_4424_:
{
lean_object* v___x_4430_; 
if (v_isShared_4419_ == 0)
{
lean_ctor_set(v___x_4418_, 0, v_a_4423_);
v___x_4430_ = v___x_4418_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4423_);
lean_ctor_set(v_reuseFailAlloc_4432_, 1, v_proof_x3f_4415_);
lean_ctor_set_uint8(v_reuseFailAlloc_4432_, sizeof(void*)*2, v_cache_4416_);
v___x_4430_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4430_, v_xs_4378_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
lean_dec_ref(v_xs_4378_);
return v___x_4431_;
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_del_object(v___x_4418_);
lean_dec(v_proof_x3f_4415_);
lean_dec_ref(v_expr_4414_);
lean_del_object(v___x_4412_);
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_xs_4378_);
v_a_4461_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4422_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4422_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_del_object(v___x_4418_);
lean_dec(v_proof_x3f_4415_);
lean_dec_ref(v_expr_4414_);
lean_del_object(v___x_4412_);
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_xs_4378_);
v_a_4469_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4420_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4420_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
}
else
{
lean_object* v_a_4480_; lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
lean_dec_ref(v___x_4402_);
lean_dec_ref(v_xs_4378_);
lean_dec_ref(v___f_4377_);
lean_dec_ref(v___f_4376_);
v_a_4480_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4482_ = v___x_4408_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_inc(v_a_4480_);
lean_dec(v___x_4408_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec(v_a_4399_);
lean_dec(v_a_4388_);
lean_dec_ref(v_xs_4378_);
lean_dec_ref(v___f_4377_);
lean_dec_ref(v___f_4376_);
lean_dec_ref(v_a_4375_);
v_a_4488_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4400_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4400_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
lean_dec(v_a_4388_);
lean_dec_ref(v_xs_4378_);
lean_dec_ref(v___f_4377_);
lean_dec_ref(v___f_4376_);
lean_dec_ref(v_a_4375_);
v_a_4496_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4398_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4398_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v_a_4388_);
lean_dec_ref(v_xs_4378_);
lean_dec_ref(v___f_4377_);
lean_dec_ref(v___f_4376_);
lean_dec_ref(v_a_4375_);
v_a_4504_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4395_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4395_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec(v_a_4388_);
lean_dec_ref(v_xs_4378_);
lean_dec_ref(v___f_4377_);
lean_dec_ref(v___f_4376_);
lean_dec_ref(v_a_4375_);
v_a_4512_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4391_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4391_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
lean_dec_ref(v_xs_4378_);
lean_dec_ref(v___f_4377_);
lean_dec_ref(v___f_4376_);
lean_dec_ref(v_a_4375_);
v_a_4520_ = lean_ctor_get(v___x_4387_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4387_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4387_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2___boxed(lean_object* v___x_4528_, lean_object* v_a_4529_, lean_object* v___f_4530_, lean_object* v___f_4531_, lean_object* v_xs_4532_, lean_object* v_x_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
uint8_t v___x_15338__boxed_4539_; lean_object* v_res_4540_; 
v___x_15338__boxed_4539_ = lean_unbox(v___x_4528_);
v_res_4540_ = l_Lean_Elab_WF_preprocess___lam__2(v___x_15338__boxed_4539_, v_a_4529_, v___f_4530_, v___f_4531_, v_xs_4532_, v_x_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec_ref(v_x_4533_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_options_4548_; lean_object* v___x_4549_; uint8_t v___x_4550_; uint8_t v___x_4551_; 
v_options_4548_ = lean_ctor_get(v_a_4545_, 2);
v___x_4549_ = l_Lean_wf_preprocess;
v___x_4550_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_options_4548_, v___x_4549_);
v___x_4551_ = 1;
if (v___x_4550_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4552_ = lean_box(0);
v___x_4553_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4553_, 0, v_e_4542_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
lean_ctor_set_uint8(v___x_4553_, sizeof(void*)*2, v___x_4551_);
v___x_4554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4553_);
return v___x_4554_;
}
else
{
lean_object* v___x_4555_; 
v___x_4555_ = l_Lean_Meta_letToHave(v_e_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___f_4557_; lean_object* v___f_4558_; lean_object* v___x_4559_; lean_object* v___f_4560_; uint8_t v___x_4561_; lean_object* v___x_4562_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc_n(v_a_4556_, 2);
lean_dec_ref_known(v___x_4555_, 1);
v___f_4557_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___f_4558_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___x_4559_ = lean_box(v___x_4551_);
v___f_4560_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__2___boxed), 11, 4);
lean_closure_set(v___f_4560_, 0, v___x_4559_);
lean_closure_set(v___f_4560_, 1, v_a_4556_);
lean_closure_set(v___f_4560_, 2, v___f_4557_);
lean_closure_set(v___f_4560_, 3, v___f_4558_);
v___x_4561_ = 0;
v___x_4562_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_a_4556_, v___f_4560_, v___x_4561_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4562_;
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
v_a_4563_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4555_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4555_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_){
_start:
{
lean_object* v_res_4577_; 
v_res_4577_ = l_Lean_Elab_WF_preprocess(v_e_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_);
lean_dec(v_a_4575_);
lean_dec_ref(v_a_4574_);
lean_dec(v_a_4573_);
lean_dec_ref(v_a_4572_);
return v_res_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4578_, lean_object* v_x_4579_, lean_object* v_x_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_){
_start:
{
lean_object* v___x_4586_; 
v___x_4586_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4578_, v_x_4579_, v_x_4580_);
return v___x_4586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4587_, lean_object* v_x_4588_, lean_object* v_x_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v_res_4595_; 
v_res_4595_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4587_, v_x_4588_, v_x_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
return v_res_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_4596_, lean_object* v_ref_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_4597_);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4602_, lean_object* v_ref_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(v_00_u03b1_4602_, v_ref_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(lean_object* v_00_u03b1_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
lean_object* v___x_4612_; 
v___x_4612_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(v_00_u03b1_4613_, v___y_4614_, v___y_4615_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_00_u03b1_4618_, lean_object* v_x_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_00_u03b1_4627_, lean_object* v_x_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_00_u03b1_4627_, v_x_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
return v_res_4635_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_wf_preprocess = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_wf_preprocess);
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_WF_wfPreprocessSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_WF_wfPreprocessSimpExtension);
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
}
#ifdef __cplusplus
}
#endif
