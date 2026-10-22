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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "paramProj"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(185, 166, 16, 253, 90, 4, 64, 220)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "paramMatcher"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(136, 249, 169, 242, 162, 242, 251, 234)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "paramLet"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value_aux_0),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value),LEAN_SCALAR_PTR_LITERAL(158, 69, 53, 139, 5, 90, 17, 138)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "transform"};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0_value;
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0 = (const lean_object*)&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_value;
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1;
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2;
static lean_once_cell_t l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0;
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
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__8 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__9 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__9_value;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__10 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__10_value;
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__11 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__11_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__12;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Attach-introduction:"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__13 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__13_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__14;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\nto"};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__15 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__15_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__16;
static const lean_string_object l_Lean_Elab_WF_preprocess___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "\ncleand up to "};
static const lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__17 = (const lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__17_value;
static lean_once_cell_t l_Lean_Elab_WF_preprocess___lam__2___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_preprocess___lam__2___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_82_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_308_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_309_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_310_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_307_, v___x_308_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10____boxed(lean_object* v_a_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_();
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(lean_object* v_k_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v_b_317_, lean_object* v_c_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
lean_inc(v___y_322_);
lean_inc_ref(v___y_321_);
lean_inc(v___y_320_);
lean_inc_ref(v___y_319_);
lean_inc(v___y_316_);
lean_inc_ref(v___y_315_);
lean_inc(v___y_314_);
v___x_324_ = lean_apply_10(v_k_313_, v_b_317_, v_c_318_, v___y_314_, v___y_315_, v___y_316_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, lean_box(0));
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object* v_k_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v_b_329_, lean_object* v_c_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(v_k_325_, v___y_326_, v___y_327_, v___y_328_, v_b_329_, v_c_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object* v_e_337_, lean_object* v_k_338_, uint8_t v_cleanupAnnotations_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v___f_348_; uint8_t v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
lean_inc(v___y_340_);
v___f_348_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_348_, 0, v_k_338_);
lean_closure_set(v___f_348_, 1, v___y_340_);
lean_closure_set(v___f_348_, 2, v___y_341_);
lean_closure_set(v___f_348_, 3, v___y_342_);
v___x_349_ = 1;
v___x_350_ = 0;
v___x_351_ = lean_box(0);
v___x_352_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_337_, v___x_349_, v___x_350_, v___x_349_, v___x_350_, v___x_351_, v___f_348_, v_cleanupAnnotations_339_, v___y_343_, v___y_344_, v___y_345_, v___y_346_);
if (lean_obj_tag(v___x_352_) == 0)
{
return v___x_352_;
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___boxed(lean_object* v_e_361_, lean_object* v_k_362_, lean_object* v_cleanupAnnotations_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_372_; lean_object* v_res_373_; 
v_cleanupAnnotations_boxed_372_ = lean_unbox(v_cleanupAnnotations_363_);
v_res_373_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_361_, v_k_362_, v_cleanupAnnotations_boxed_372_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_object* v_00_u03b1_374_, lean_object* v_e_375_, lean_object* v_k_376_, uint8_t v_cleanupAnnotations_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_375_, v_k_376_, v_cleanupAnnotations_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___boxed(lean_object* v_00_u03b1_387_, lean_object* v_e_388_, lean_object* v_k_389_, lean_object* v_cleanupAnnotations_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_399_; lean_object* v_res_400_; 
v_cleanupAnnotations_boxed_399_ = lean_unbox(v_cleanupAnnotations_390_);
v_res_400_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(v_00_u03b1_387_, v_e_388_, v_k_389_, v_cleanupAnnotations_boxed_399_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(size_t v_sz_401_, size_t v_i_402_, lean_object* v_bs_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_usize_dec_lt(v_i_402_, v_sz_401_);
if (v___x_404_ == 0)
{
return v_bs_403_;
}
else
{
lean_object* v_v_405_; lean_object* v___x_406_; lean_object* v_bs_x27_407_; lean_object* v___y_409_; lean_object* v___x_414_; 
v_v_405_ = lean_array_uget(v_bs_403_, v_i_402_);
v___x_406_ = lean_unsigned_to_nat(0u);
v_bs_x27_407_ = lean_array_uset(v_bs_403_, v_i_402_, v___x_406_);
v___x_414_ = l_Lean_Elab_WF_isWfParam_x3f(v_v_405_);
if (lean_obj_tag(v___x_414_) == 0)
{
v___y_409_ = v_v_405_;
goto v___jp_408_;
}
else
{
lean_object* v_val_415_; 
lean_dec(v_v_405_);
v_val_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v___x_414_, 1);
v___y_409_ = v_val_415_;
goto v___jp_408_;
}
v___jp_408_:
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_402_, v___x_410_);
v___x_412_ = lean_array_uset(v_bs_x27_407_, v_i_402_, v___y_409_);
v_i_402_ = v___x_411_;
v_bs_403_ = v___x_412_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___boxed(lean_object* v_sz_416_, lean_object* v_i_417_, lean_object* v_bs_418_){
_start:
{
size_t v_sz_boxed_419_; size_t v_i_boxed_420_; lean_object* v_res_421_; 
v_sz_boxed_419_ = lean_unbox_usize(v_sz_416_);
lean_dec(v_sz_416_);
v_i_boxed_420_ = lean_unbox_usize(v_i_417_);
lean_dec(v_i_417_);
v_res_421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_boxed_419_, v_i_boxed_420_, v_bs_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(lean_object* v_msgData_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_428_; lean_object* v_env_429_; uint8_t v___x_430_; lean_object* v_env_431_; lean_object* v___x_432_; lean_object* v_toCold_433_; lean_object* v_mctx_434_; lean_object* v_lctx_435_; lean_object* v_options_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_428_ = lean_st_ref_get(v___y_426_);
v_env_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_ref(v_env_429_);
lean_dec(v___x_428_);
v___x_430_ = 0;
v_env_431_ = l_Lean_Environment_setRecordingDeps(v_env_429_, v___x_430_);
v___x_432_ = lean_st_ref_get(v___y_424_);
v_toCold_433_ = lean_ctor_get(v___y_425_, 0);
v_mctx_434_ = lean_ctor_get(v___x_432_, 0);
lean_inc_ref(v_mctx_434_);
lean_dec(v___x_432_);
v_lctx_435_ = lean_ctor_get(v___y_423_, 2);
v_options_436_ = lean_ctor_get(v_toCold_433_, 2);
lean_inc_ref(v_options_436_);
lean_inc_ref(v_lctx_435_);
v___x_437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_437_, 0, v_env_431_);
lean_ctor_set(v___x_437_, 1, v_mctx_434_);
lean_ctor_set(v___x_437_, 2, v_lctx_435_);
lean_ctor_set(v___x_437_, 3, v_options_436_);
v___x_438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_msgData_422_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16___boxed(lean_object* v_msgData_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msgData_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_ref_453_; lean_object* v___x_454_; lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_ref_453_ = lean_ctor_get(v___y_450_, 2);
v___x_454_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_463_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_inc(v_ref_453_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_ref_453_);
lean_ctor_set(v___x_459_, 1, v_a_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set_tag(v___x_457_, 1);
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg___boxed(lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(lean_object* v_ref_471_, lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_toCold_481_; lean_object* v_currRecDepth_482_; lean_object* v_ref_483_; uint16_t v_optionFlags_484_; uint8_t v_suppressElabErrors_485_; uint8_t v_isRecordingDeps_486_; lean_object* v_ref_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_toCold_481_ = lean_ctor_get(v___y_478_, 0);
v_currRecDepth_482_ = lean_ctor_get(v___y_478_, 1);
v_ref_483_ = lean_ctor_get(v___y_478_, 2);
v_optionFlags_484_ = lean_ctor_get_uint16(v___y_478_, sizeof(void*)*3);
v_suppressElabErrors_485_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 2);
v_isRecordingDeps_486_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 3);
v_ref_487_ = l_Lean_replaceRef(v_ref_471_, v_ref_483_);
lean_inc(v_currRecDepth_482_);
lean_inc_ref(v_toCold_481_);
v___x_488_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_488_, 0, v_toCold_481_);
lean_ctor_set(v___x_488_, 1, v_currRecDepth_482_);
lean_ctor_set(v___x_488_, 2, v_ref_487_);
lean_ctor_set_uint16(v___x_488_, sizeof(void*)*3, v_optionFlags_484_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*3 + 2, v_suppressElabErrors_485_);
lean_ctor_set_uint8(v___x_488_, sizeof(void*)*3 + 3, v_isRecordingDeps_486_);
v___x_489_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_472_, v___y_476_, v___y_477_, v___x_488_, v___y_479_);
lean_dec_ref_known(v___x_488_, 3);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_490_, lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_490_, v_msg_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec(v_ref_490_);
return v_res_500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_504_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
lean_ctor_set(v___x_506_, 2, v___x_505_);
lean_ctor_set(v___x_506_, 3, v___x_505_);
lean_ctor_set(v___x_506_, 4, v___x_504_);
lean_ctor_set(v___x_506_, 5, v___x_504_);
lean_ctor_set(v___x_506_, 6, v___x_504_);
lean_ctor_set(v___x_506_, 7, v___x_504_);
lean_ctor_set(v___x_506_, 8, v___x_504_);
lean_ctor_set(v___x_506_, 9, v___x_504_);
lean_ctor_set(v___x_506_, 10, v___x_503_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_unsigned_to_nat(32u);
v___x_508_ = lean_mk_empty_array_with_capacity(v___x_507_);
v___x_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_510_ = ((size_t)5ULL);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = lean_unsigned_to_nat(32u);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_512_);
v___x_514_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_515_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v___x_513_);
lean_ctor_set(v___x_515_, 2, v___x_511_);
lean_ctor_set(v___x_515_, 3, v___x_511_);
lean_ctor_set_usize(v___x_515_, 4, v___x_510_);
return v___x_515_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = lean_box(1);
v___x_517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
lean_ctor_set(v___x_519_, 1, v___x_517_);
lean_ctor_set(v___x_519_, 2, v___x_516_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_522_ = l_Lean_stringToMessageData(v___x_521_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_525_ = l_Lean_stringToMessageData(v___x_524_);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_528_ = l_Lean_stringToMessageData(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_541_, lean_object* v_declHint_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v_env_547_; uint8_t v___x_548_; 
v___x_545_ = lean_box(0);
v___x_546_ = lean_st_ref_get(v___y_543_);
v_env_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc_ref(v_env_547_);
lean_dec(v___x_546_);
v___x_548_ = l_Lean_Name_isAnonymous(v_declHint_542_);
if (v___x_548_ == 0)
{
uint8_t v_isExporting_549_; 
v_isExporting_549_ = lean_ctor_get_uint8(v_env_547_, sizeof(void*)*13);
if (v_isExporting_549_ == 0)
{
lean_object* v___x_550_; 
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_550_, 0, v_msg_541_);
return v___x_550_;
}
else
{
lean_object* v___x_551_; uint8_t v___x_552_; 
lean_inc_ref(v_env_547_);
v___x_551_ = l_Lean_Environment_setExporting(v_env_547_, v___x_548_);
lean_inc(v_declHint_542_);
lean_inc_ref(v___x_551_);
v___x_552_ = l_Lean_Environment_contains(v___x_551_, v_declHint_542_, v_isExporting_549_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v___x_551_);
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_msg_541_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_c_559_; lean_object* v___x_560_; 
v___x_554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_556_ = l_Lean_Options_empty;
v___x_557_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_557_, 0, v___x_551_);
lean_ctor_set(v___x_557_, 1, v___x_554_);
lean_ctor_set(v___x_557_, 2, v___x_555_);
lean_ctor_set(v___x_557_, 3, v___x_556_);
lean_inc(v_declHint_542_);
v___x_558_ = l_Lean_MessageData_ofConstName(v_declHint_542_, v___x_548_);
v_c_559_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_559_, 0, v___x_557_);
lean_ctor_set(v_c_559_, 1, v___x_558_);
v___x_560_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_547_, v_declHint_542_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_561_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
lean_ctor_set(v___x_562_, 1, v_c_559_);
v___x_563_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_MessageData_note(v___x_564_);
v___x_566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_566_, 0, v_msg_541_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
else
{
lean_object* v_val_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_602_; 
v_val_568_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_602_ == 0)
{
v___x_570_ = v___x_560_;
v_isShared_571_ = v_isSharedCheck_602_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_val_568_);
lean_dec(v___x_560_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_602_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v_moduleNames_573_; lean_object* v_mod_574_; uint8_t v___x_575_; 
v___x_572_ = l_Lean_Environment_header(v_env_547_);
lean_dec_ref(v_env_547_);
v_moduleNames_573_ = lean_ctor_get(v___x_572_, 4);
lean_inc_ref(v_moduleNames_573_);
lean_dec_ref(v___x_572_);
v_mod_574_ = lean_array_get(v___x_545_, v_moduleNames_573_, v_val_568_);
lean_dec(v_val_568_);
lean_dec_ref(v_moduleNames_573_);
v___x_575_ = l_Lean_isPrivateName(v_declHint_542_);
lean_dec(v_declHint_542_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_576_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_c_559_);
v___x_578_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_MessageData_ofName(v_mod_574_);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = l_Lean_MessageData_note(v___x_583_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v_msg_541_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
lean_ctor_set(v___x_570_, 0, v___x_585_);
v___x_587_ = v___x_570_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_600_; 
v___x_589_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v_c_559_);
v___x_591_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = l_Lean_MessageData_ofName(v_mod_574_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_MessageData_note(v___x_596_);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v_msg_541_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
if (v_isShared_571_ == 0)
{
lean_ctor_set_tag(v___x_570_, 0);
lean_ctor_set(v___x_570_, 0, v___x_598_);
v___x_600_ = v___x_570_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v___x_598_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_603_; 
lean_dec_ref(v_env_547_);
lean_dec(v_declHint_542_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v_msg_541_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_604_, lean_object* v_declHint_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_604_, v_declHint_605_, v___y_606_);
lean_dec(v___y_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object* v_msg_609_, lean_object* v_declHint_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_629_; 
v___x_619_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_609_, v_declHint_610_, v___y_617_);
v_a_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_629_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_629_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_624_ = l_Lean_unknownIdentifierMessageTag;
v___x_625_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v_a_620_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_625_);
v___x_627_ = v___x_622_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_630_, lean_object* v_declHint_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_630_, v_declHint_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_ref_641_, lean_object* v_msg_642_, lean_object* v_declHint_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v___x_652_; lean_object* v_a_653_; lean_object* v___x_654_; 
v___x_652_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_642_, v_declHint_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref(v___x_652_);
v___x_654_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_641_, v_a_653_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_ref_655_, lean_object* v_msg_656_, lean_object* v_declHint_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_655_, v_msg_656_, v_declHint_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec(v___y_662_);
lean_dec_ref(v___y_661_);
lean_dec(v___y_660_);
lean_dec_ref(v___y_659_);
lean_dec(v___y_658_);
lean_dec(v_ref_655_);
return v_res_666_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0));
v___x_669_ = l_Lean_stringToMessageData(v___x_668_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2));
v___x_672_ = l_Lean_stringToMessageData(v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_ref_673_, lean_object* v_constName_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; uint8_t v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_683_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_684_ = 0;
lean_inc(v_constName_674_);
v___x_685_ = l_Lean_MessageData_ofConstName(v_constName_674_, v___x_684_);
v___x_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_683_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3);
v___x_688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v___x_689_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_673_, v___x_688_, v_constName_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_ref_690_, lean_object* v_constName_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_690_, v_constName_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
lean_dec(v___y_692_);
lean_dec(v_ref_690_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_ref_710_; lean_object* v___x_711_; 
v_ref_710_ = lean_ctor_get(v___y_707_, 2);
v___x_711_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_710_, v_constName_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object* v_constName_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; lean_object* v_env_732_; uint8_t v___x_733_; lean_object* v___x_734_; 
v___x_731_ = lean_st_ref_get(v___y_729_);
v_env_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc_ref(v_env_732_);
lean_dec(v___x_731_);
v___x_733_ = 0;
lean_inc(v_constName_722_);
v___x_734_ = l_Lean_Environment_find_x3f(v_env_732_, v_constName_722_, v___x_733_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
return v___x_735_;
}
else
{
lean_object* v_val_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v_constName_722_);
v_val_736_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_734_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_val_736_);
lean_dec(v___x_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 0);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_val_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object* v_constName_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
return v_res_753_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_instMonadEIO___redArg();
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object* v_msg_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v_toApplicative_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_834_; 
v___x_768_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0);
v___x_769_ = l_StateRefT_x27_instMonad___redArg(v___x_768_);
v_toApplicative_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_769_, 1);
lean_dec(v_unused_835_);
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_834_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_toApplicative_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_834_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_toFunctor_774_; lean_object* v_toSeq_775_; lean_object* v_toSeqLeft_776_; lean_object* v_toSeqRight_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_832_; 
v_toFunctor_774_ = lean_ctor_get(v_toApplicative_770_, 0);
v_toSeq_775_ = lean_ctor_get(v_toApplicative_770_, 2);
v_toSeqLeft_776_ = lean_ctor_get(v_toApplicative_770_, 3);
v_toSeqRight_777_ = lean_ctor_get(v_toApplicative_770_, 4);
v_isSharedCheck_832_ = !lean_is_exclusive(v_toApplicative_770_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_toApplicative_770_, 1);
lean_dec(v_unused_833_);
v___x_779_ = v_toApplicative_770_;
v_isShared_780_ = v_isSharedCheck_832_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_toSeqRight_777_);
lean_inc(v_toSeqLeft_776_);
lean_inc(v_toSeq_775_);
lean_inc(v_toFunctor_774_);
lean_dec(v_toApplicative_770_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_832_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___f_781_; lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___x_790_; 
v___f_781_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1));
v___f_782_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_774_);
v___f_783_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_783_, 0, v_toFunctor_774_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_774_);
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v___f_783_);
lean_ctor_set(v___x_785_, 1, v___f_784_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_786_, 0, v_toSeqRight_777_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqLeft_776_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeq_775_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v___f_786_);
lean_ctor_set(v___x_779_, 3, v___f_787_);
lean_ctor_set(v___x_779_, 2, v___f_788_);
lean_ctor_set(v___x_779_, 1, v___f_781_);
lean_ctor_set(v___x_779_, 0, v___x_785_);
v___x_790_ = v___x_779_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___f_781_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v___f_788_);
lean_ctor_set(v_reuseFailAlloc_831_, 3, v___f_787_);
lean_ctor_set(v_reuseFailAlloc_831_, 4, v___f_786_);
v___x_790_ = v_reuseFailAlloc_831_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
lean_object* v___x_792_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___f_782_);
lean_ctor_set(v___x_772_, 0, v___x_790_);
v___x_792_ = v___x_772_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v___f_782_);
v___x_792_ = v_reuseFailAlloc_830_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v_toApplicative_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_828_; 
v___x_793_ = l_StateRefT_x27_instMonad___redArg(v___x_792_);
v_toApplicative_794_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v___x_793_, 1);
lean_dec(v_unused_829_);
v___x_796_ = v___x_793_;
v_isShared_797_ = v_isSharedCheck_828_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_toApplicative_794_);
lean_dec(v___x_793_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_828_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_toFunctor_798_; lean_object* v_toSeq_799_; lean_object* v_toSeqLeft_800_; lean_object* v_toSeqRight_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_826_; 
v_toFunctor_798_ = lean_ctor_get(v_toApplicative_794_, 0);
v_toSeq_799_ = lean_ctor_get(v_toApplicative_794_, 2);
v_toSeqLeft_800_ = lean_ctor_get(v_toApplicative_794_, 3);
v_toSeqRight_801_ = lean_ctor_get(v_toApplicative_794_, 4);
v_isSharedCheck_826_ = !lean_is_exclusive(v_toApplicative_794_);
if (v_isSharedCheck_826_ == 0)
{
lean_object* v_unused_827_; 
v_unused_827_ = lean_ctor_get(v_toApplicative_794_, 1);
lean_dec(v_unused_827_);
v___x_803_ = v_toApplicative_794_;
v_isShared_804_ = v_isSharedCheck_826_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_toSeqRight_801_);
lean_inc(v_toSeqLeft_800_);
lean_inc(v_toSeq_799_);
lean_inc(v_toFunctor_798_);
lean_dec(v_toApplicative_794_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_826_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___x_809_; lean_object* v___f_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___x_814_; 
v___f_805_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3));
v___f_806_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_798_);
v___f_807_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_807_, 0, v_toFunctor_798_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_808_, 0, v_toFunctor_798_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___f_807_);
lean_ctor_set(v___x_809_, 1, v___f_808_);
v___f_810_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_810_, 0, v_toSeqRight_801_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_811_, 0, v_toSeqLeft_800_);
v___f_812_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_812_, 0, v_toSeq_799_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 4, v___f_810_);
lean_ctor_set(v___x_803_, 3, v___f_811_);
lean_ctor_set(v___x_803_, 2, v___f_812_);
lean_ctor_set(v___x_803_, 1, v___f_805_);
lean_ctor_set(v___x_803_, 0, v___x_809_);
v___x_814_ = v___x_803_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___f_805_);
lean_ctor_set(v_reuseFailAlloc_825_, 2, v___f_812_);
lean_ctor_set(v_reuseFailAlloc_825_, 3, v___f_811_);
lean_ctor_set(v_reuseFailAlloc_825_, 4, v___f_810_);
v___x_814_ = v_reuseFailAlloc_825_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_816_; 
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___f_806_);
lean_ctor_set(v___x_796_, 0, v___x_814_);
v___x_816_ = v___x_796_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_824_, 1, v___f_806_);
v___x_816_ = v_reuseFailAlloc_824_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_13046__overap_822_; lean_object* v___x_823_; 
v___x_817_ = l_StateRefT_x27_instMonad___redArg(v___x_816_);
v___x_818_ = l_ReaderT_instMonad___redArg(v___x_817_);
v___x_819_ = l_ReaderT_instMonad___redArg(v___x_818_);
v___x_820_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_821_ = l_instInhabitedOfMonad___redArg(v___x_819_, v___x_820_);
v___x_13046__overap_822_ = lean_panic_fn_borrowed(v___x_821_, v_msg_759_);
lean_dec(v___x_821_);
lean_inc(v___y_766_);
lean_inc_ref(v___y_765_);
lean_inc(v___y_764_);
lean_inc_ref(v___y_763_);
lean_inc(v___y_762_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
v___x_823_ = lean_apply_8(v___x_13046__overap_822_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, lean_box(0));
return v___x_823_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object* v_msg_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
return v_res_845_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2));
v___x_850_ = lean_unsigned_to_nat(53u);
v___x_851_ = lean_unsigned_to_nat(62u);
v___x_852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1));
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0));
v___x_854_ = l_mkPanicMessageWithDecl(v___x_853_, v___x_852_, v___x_851_, v___x_850_, v___x_849_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t v_sz_855_, size_t v_i_856_, lean_object* v_bs_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
uint8_t v___x_866_; 
v___x_866_ = lean_usize_dec_lt(v_i_856_, v_sz_855_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v_bs_857_);
return v___x_867_;
}
else
{
lean_object* v_v_868_; lean_object* v___x_869_; lean_object* v_bs_x27_870_; lean_object* v_a_872_; lean_object* v___x_877_; 
v_v_868_ = lean_array_uget(v_bs_857_, v_i_856_);
v___x_869_ = lean_unsigned_to_nat(0u);
v_bs_x27_870_ = lean_array_uset(v_bs_857_, v_i_856_, v___x_869_);
v___x_877_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_v_868_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
if (lean_obj_tag(v_a_878_) == 6)
{
lean_object* v_val_879_; lean_object* v_numFields_880_; uint8_t v___x_881_; lean_object* v___x_882_; 
v_val_879_ = lean_ctor_get(v_a_878_, 0);
lean_inc_ref(v_val_879_);
lean_dec_ref_known(v_a_878_, 1);
v_numFields_880_ = lean_ctor_get(v_val_879_, 4);
lean_inc(v_numFields_880_);
lean_dec_ref(v_val_879_);
v___x_881_ = 0;
v___x_882_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_882_, 0, v_numFields_880_);
lean_ctor_set(v___x_882_, 1, v___x_869_);
lean_ctor_set_uint8(v___x_882_, sizeof(void*)*2, v___x_881_);
v_a_872_ = v___x_882_;
goto v___jp_871_;
}
else
{
lean_object* v___x_883_; lean_object* v___x_884_; 
lean_dec(v_a_878_);
v___x_883_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3);
v___x_884_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v___x_883_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v_a_872_ = v_a_885_;
goto v___jp_871_;
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_bs_x27_870_);
v_a_886_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_884_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_884_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v_bs_x27_870_);
v_a_894_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_877_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_877_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
v___jp_871_:
{
size_t v___x_873_; size_t v___x_874_; lean_object* v___x_875_; 
v___x_873_ = ((size_t)1ULL);
v___x_874_ = lean_usize_add(v_i_856_, v___x_873_);
v___x_875_ = lean_array_uset(v_bs_x27_870_, v_i_856_, v_a_872_);
v_i_856_ = v___x_874_;
v_bs_857_ = v___x_875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object* v_sz_902_, lean_object* v_i_903_, lean_object* v_bs_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
size_t v_sz_boxed_913_; size_t v_i_boxed_914_; lean_object* v_res_915_; 
v_sz_boxed_913_ = lean_unbox_usize(v_sz_902_);
lean_dec(v_sz_902_);
v_i_boxed_914_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_boxed_913_, v_i_boxed_914_, v_bs_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object* v_declName_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; lean_object* v_env_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_919_ = lean_st_ref_get(v___y_917_);
v_env_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_ref(v_env_920_);
lean_dec(v___x_919_);
v___x_921_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_920_, v_declName_916_);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object* v_declName_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_923_, v___y_924_);
lean_dec(v___y_924_);
return v_res_926_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_927_; lean_object* v_dummy_928_; 
v___x_927_ = lean_box(0);
v_dummy_928_ = l_Lean_Expr_sort___override(v___x_927_);
return v_dummy_928_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_box(0);
v___x_930_ = lean_unsigned_to_nat(16u);
v___x_931_ = lean_mk_array(v___x_930_, v___x_929_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object* v_e_937_, uint8_t v_alsoCasesOn_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
uint8_t v___x_950_; 
v___x_950_ = l_Lean_Expr_isApp(v_e_937_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec_ref(v_e_937_);
v___x_951_ = lean_box(0);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Expr_getAppFn(v_e_937_);
if (lean_obj_tag(v___x_953_) == 4)
{
lean_object* v_declName_954_; lean_object* v_us_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_1110_; 
v_declName_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc_n(v_declName_954_, 2);
v_us_955_ = lean_ctor_get(v___x_953_, 1);
lean_inc(v_us_955_);
lean_dec_ref_known(v___x_953_, 2);
v___x_956_ = l_Lean_instInhabitedExpr;
v___x_957_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_954_, v___y_945_);
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_1110_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_1110_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
if (lean_obj_tag(v_a_958_) == 1)
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1003_; 
v_val_962_ = lean_ctor_get(v_a_958_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_a_958_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_964_ = v_a_958_;
v_isShared_965_ = v_isSharedCheck_1003_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v_a_958_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1003_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v_dummy_966_; lean_object* v_nargs_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v_args_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_dummy_966_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_967_ = l_Lean_Expr_getAppNumArgs(v_e_937_);
lean_inc(v_nargs_967_);
v___x_968_ = lean_mk_array(v_nargs_967_, v_dummy_966_);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = lean_nat_sub(v_nargs_967_, v___x_969_);
lean_dec(v_nargs_967_);
v_args_971_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_937_, v___x_968_, v___x_970_);
v___x_972_ = lean_array_get_size(v_args_971_);
v___x_973_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_962_);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v_numParams_975_; lean_object* v_numDiscrs_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v_numParams_975_ = lean_ctor_get(v_val_962_, 0);
v_numDiscrs_976_ = lean_ctor_get(v_val_962_, 1);
v___x_977_ = lean_array_mk(v_us_955_);
v___x_978_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_975_);
v___x_979_ = l_Array_extract___redArg(v_args_971_, v___x_978_, v_numParams_975_);
v___x_980_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_962_);
v___x_981_ = lean_array_get(v___x_956_, v_args_971_, v___x_980_);
lean_dec(v___x_980_);
v___x_982_ = lean_nat_add(v_numParams_975_, v___x_969_);
v___x_983_ = lean_nat_add(v___x_982_, v_numDiscrs_976_);
lean_inc(v___x_983_);
lean_inc_ref_n(v_args_971_, 2);
v___x_984_ = l_Array_toSubarray___redArg(v_args_971_, v___x_982_, v___x_983_);
v___x_985_ = l_Subarray_copy___redArg(v___x_984_);
v___x_986_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_962_);
v___x_987_ = lean_nat_add(v___x_983_, v___x_986_);
lean_dec(v___x_986_);
lean_inc(v___x_987_);
v___x_988_ = l_Array_toSubarray___redArg(v_args_971_, v___x_983_, v___x_987_);
v___x_989_ = l_Subarray_copy___redArg(v___x_988_);
v___x_990_ = l_Array_toSubarray___redArg(v_args_971_, v___x_987_, v___x_972_);
v___x_991_ = l_Subarray_copy___redArg(v___x_990_);
v___x_992_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_992_, 0, v_val_962_);
lean_ctor_set(v___x_992_, 1, v_declName_954_);
lean_ctor_set(v___x_992_, 2, v___x_977_);
lean_ctor_set(v___x_992_, 3, v___x_979_);
lean_ctor_set(v___x_992_, 4, v___x_981_);
lean_ctor_set(v___x_992_, 5, v___x_985_);
lean_ctor_set(v___x_992_, 6, v___x_989_);
lean_ctor_set(v___x_992_, 7, v___x_991_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_992_);
v___x_994_ = v___x_964_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_992_);
v___x_994_ = v_reuseFailAlloc_998_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_996_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_994_);
v___x_996_ = v___x_960_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec_ref(v_args_971_);
lean_del_object(v___x_964_);
lean_dec(v_val_962_);
lean_dec(v_us_955_);
lean_dec(v_declName_954_);
v___x_999_ = lean_box(0);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_999_);
v___x_1001_ = v___x_960_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v___x_1004_; 
lean_del_object(v___x_960_);
lean_dec(v_a_958_);
v___x_1004_ = lean_st_ref_get(v___y_945_);
if (v_alsoCasesOn_938_ == 0)
{
lean_dec(v___x_1004_);
lean_dec(v_us_955_);
lean_dec(v_declName_954_);
lean_dec_ref(v_e_937_);
goto v___jp_947_;
}
else
{
lean_object* v_env_1005_; uint8_t v___x_1006_; 
v_env_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc_ref(v_env_1005_);
lean_dec(v___x_1004_);
lean_inc(v_declName_954_);
v___x_1006_ = l_Lean_isCasesOnRecursor(v_env_1005_, v_declName_954_);
if (v___x_1006_ == 0)
{
lean_dec(v_us_955_);
lean_dec(v_declName_954_);
lean_dec_ref(v_e_937_);
goto v___jp_947_;
}
else
{
lean_object* v_indName_1007_; lean_object* v___x_1008_; 
v_indName_1007_ = l_Lean_Name_getPrefix(v_declName_954_);
v___x_1008_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_indName_1007_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1101_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1011_ = v___x_1008_;
v_isShared_1012_ = v_isSharedCheck_1101_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1101_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
if (lean_obj_tag(v_a_1009_) == 5)
{
lean_object* v_val_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1096_; 
v_val_1013_ = lean_ctor_get(v_a_1009_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_a_1009_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1015_ = v_a_1009_;
v_isShared_1016_ = v_isSharedCheck_1096_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_val_1013_);
lean_dec(v_a_1009_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1096_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_toConstantVal_1017_; lean_object* v_numParams_1018_; lean_object* v_numIndices_1019_; lean_object* v_ctors_1020_; lean_object* v_nargs_1021_; lean_object* v_dummy_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_args_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_toConstantVal_1017_ = lean_ctor_get(v_val_1013_, 0);
lean_inc_ref(v_toConstantVal_1017_);
v_numParams_1018_ = lean_ctor_get(v_val_1013_, 1);
lean_inc(v_numParams_1018_);
v_numIndices_1019_ = lean_ctor_get(v_val_1013_, 2);
lean_inc(v_numIndices_1019_);
v_ctors_1020_ = lean_ctor_get(v_val_1013_, 4);
lean_inc(v_ctors_1020_);
v_nargs_1021_ = l_Lean_Expr_getAppNumArgs(v_e_937_);
v_dummy_1022_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
lean_inc(v_nargs_1021_);
v___x_1023_ = lean_mk_array(v_nargs_1021_, v_dummy_1022_);
v___x_1024_ = lean_unsigned_to_nat(1u);
v___x_1025_ = lean_nat_sub(v_nargs_1021_, v___x_1024_);
lean_dec(v_nargs_1021_);
v_args_1026_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_937_, v___x_1023_, v___x_1025_);
v___x_1027_ = lean_nat_add(v_numParams_1018_, v___x_1024_);
v___x_1028_ = lean_nat_add(v___x_1027_, v_numIndices_1019_);
v___x_1029_ = lean_nat_add(v___x_1028_, v___x_1024_);
lean_dec(v___x_1028_);
v___x_1030_ = l_Lean_InductiveVal_numCtors(v_val_1013_);
lean_dec_ref(v_val_1013_);
v___x_1031_ = lean_nat_add(v___x_1029_, v___x_1030_);
lean_dec(v___x_1030_);
v___x_1032_ = lean_array_get_size(v_args_1026_);
v___x_1033_ = lean_nat_dec_le(v___x_1031_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_dec(v___x_1031_);
lean_dec(v___x_1029_);
lean_dec(v___x_1027_);
lean_dec_ref(v_args_1026_);
lean_dec(v_ctors_1020_);
lean_dec(v_numIndices_1019_);
lean_dec(v_numParams_1018_);
lean_dec_ref(v_toConstantVal_1017_);
lean_del_object(v___x_1015_);
lean_dec(v_us_955_);
lean_dec(v_declName_954_);
v___x_1034_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1034_);
v___x_1036_ = v___x_1011_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v_params_1039_; lean_object* v_motive_1040_; lean_object* v_discrs_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v_discrInfos_1044_; lean_object* v_alts_1045_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v_lower_1087_; lean_object* v_upper_1088_; uint8_t v___x_1095_; 
lean_del_object(v___x_1011_);
v___x_1038_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1018_);
lean_inc_ref_n(v_args_1026_, 3);
v_params_1039_ = l_Array_toSubarray___redArg(v_args_1026_, v___x_1038_, v_numParams_1018_);
v_motive_1040_ = lean_array_get(v___x_956_, v_args_1026_, v_numParams_1018_);
lean_dec(v_numParams_1018_);
lean_inc(v___x_1029_);
v_discrs_1041_ = l_Array_toSubarray___redArg(v_args_1026_, v___x_1027_, v___x_1029_);
v___x_1042_ = lean_nat_add(v_numIndices_1019_, v___x_1024_);
lean_dec(v_numIndices_1019_);
v___x_1043_ = lean_box(0);
v_discrInfos_1044_ = lean_mk_array(v___x_1042_, v___x_1043_);
lean_inc(v___x_1031_);
v_alts_1045_ = l_Array_toSubarray___redArg(v_args_1026_, v___x_1029_, v___x_1031_);
v___x_1095_ = lean_nat_dec_le(v___x_1031_, v___x_1038_);
if (v___x_1095_ == 0)
{
v_lower_1087_ = v___x_1031_;
v_upper_1088_ = v___x_1032_;
goto v___jp_1086_;
}
else
{
lean_dec(v___x_1031_);
v_lower_1087_ = v___x_1038_;
v_upper_1088_ = v___x_1032_;
goto v___jp_1086_;
}
v___jp_1046_:
{
lean_object* v___x_1049_; size_t v_sz_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_array_mk(v_ctors_1020_);
v_sz_1050_ = lean_array_size(v___x_1049_);
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_1050_, v___x_1051_, v___x_1049_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1077_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1055_ = v___x_1052_;
v_isShared_1056_ = v_isSharedCheck_1077_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_a_1053_);
lean_dec(v___x_1052_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1077_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v_start_1057_; lean_object* v_stop_1058_; lean_object* v_start_1059_; lean_object* v_stop_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_start_1057_ = lean_ctor_get(v_params_1039_, 1);
v_stop_1058_ = lean_ctor_get(v_params_1039_, 2);
v_start_1059_ = lean_ctor_get(v_discrs_1041_, 1);
v_stop_1060_ = lean_ctor_get(v_discrs_1041_, 2);
v___x_1061_ = lean_nat_sub(v_stop_1058_, v_start_1057_);
v___x_1062_ = lean_nat_sub(v_stop_1060_, v_start_1059_);
v___x_1063_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2);
v___x_1064_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1061_);
lean_ctor_set(v___x_1064_, 1, v___x_1062_);
lean_ctor_set(v___x_1064_, 2, v_a_1053_);
lean_ctor_set(v___x_1064_, 3, v___y_1048_);
lean_ctor_set(v___x_1064_, 4, v_discrInfos_1044_);
lean_ctor_set(v___x_1064_, 5, v___x_1063_);
v___x_1065_ = lean_array_mk(v_us_955_);
v___x_1066_ = l_Subarray_copy___redArg(v_params_1039_);
v___x_1067_ = l_Subarray_copy___redArg(v_discrs_1041_);
v___x_1068_ = l_Subarray_copy___redArg(v_alts_1045_);
v___x_1069_ = l_Subarray_copy___redArg(v___y_1047_);
v___x_1070_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1064_);
lean_ctor_set(v___x_1070_, 1, v_declName_954_);
lean_ctor_set(v___x_1070_, 2, v___x_1065_);
lean_ctor_set(v___x_1070_, 3, v___x_1066_);
lean_ctor_set(v___x_1070_, 4, v_motive_1040_);
lean_ctor_set(v___x_1070_, 5, v___x_1067_);
lean_ctor_set(v___x_1070_, 6, v___x_1068_);
lean_ctor_set(v___x_1070_, 7, v___x_1069_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 1);
lean_ctor_set(v___x_1015_, 0, v___x_1070_);
v___x_1072_ = v___x_1015_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
lean_object* v___x_1074_; 
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 0, v___x_1072_);
v___x_1074_ = v___x_1055_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
else
{
lean_object* v_a_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1085_; 
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec_ref(v_alts_1045_);
lean_dec_ref(v_discrInfos_1044_);
lean_dec_ref(v_discrs_1041_);
lean_dec(v_motive_1040_);
lean_dec_ref(v_params_1039_);
lean_del_object(v___x_1015_);
lean_dec(v_us_955_);
lean_dec(v_declName_954_);
v_a_1078_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1080_ = v___x_1052_;
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_a_1078_);
lean_dec(v___x_1052_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1085_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1083_; 
if (v_isShared_1081_ == 0)
{
v___x_1083_ = v___x_1080_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v_a_1078_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
v___jp_1086_:
{
lean_object* v_levelParams_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_levelParams_1089_ = lean_ctor_get(v_toConstantVal_1017_, 1);
lean_inc(v_levelParams_1089_);
lean_dec_ref(v_toConstantVal_1017_);
v___x_1090_ = l_Array_toSubarray___redArg(v_args_1026_, v_lower_1087_, v_upper_1088_);
v___x_1091_ = l_List_lengthTR___redArg(v_levelParams_1089_);
lean_dec(v_levelParams_1089_);
v___x_1092_ = l_List_lengthTR___redArg(v_us_955_);
v___x_1093_ = lean_nat_dec_eq(v___x_1091_, v___x_1092_);
lean_dec(v___x_1092_);
lean_dec(v___x_1091_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3));
v___y_1047_ = v___x_1090_;
v___y_1048_ = v___x_1094_;
goto v___jp_1046_;
}
else
{
v___y_1047_ = v___x_1090_;
v___y_1048_ = v___x_1043_;
goto v___jp_1046_;
}
}
}
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_dec(v_a_1009_);
lean_dec(v_us_955_);
lean_dec(v_declName_954_);
lean_dec_ref(v_e_937_);
v___x_1097_ = lean_box(0);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 0, v___x_1097_);
v___x_1099_ = v___x_1011_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_us_955_);
lean_dec(v_declName_954_);
lean_dec_ref(v_e_937_);
v_a_1102_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1008_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1008_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
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
lean_dec_ref(v___x_953_);
lean_dec_ref(v_e_937_);
goto v___jp_947_;
}
}
v___jp_947_:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object* v_e_1111_, lean_object* v_alsoCasesOn_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1121_; lean_object* v_res_1122_; 
v_alsoCasesOn_boxed_1121_ = lean_unbox(v_alsoCasesOn_1112_);
v_res_1122_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1111_, v_alsoCasesOn_boxed_1121_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
lean_dec(v___y_1113_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t v_sz_1123_, size_t v_i_1124_, lean_object* v_bs_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_usize_dec_lt(v_i_1124_, v_sz_1123_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v_bs_1125_);
return v___x_1132_;
}
else
{
lean_object* v_v_1133_; lean_object* v___x_1134_; lean_object* v_bs_x27_1135_; lean_object* v___x_1136_; 
v_v_1133_ = lean_array_uget(v_bs_1125_, v_i_1124_);
v___x_1134_ = lean_unsigned_to_nat(0u);
v_bs_x27_1135_ = lean_array_uset(v_bs_1125_, v_i_1124_, v___x_1134_);
v___x_1136_ = l_Lean_Elab_WF_mkWfParam(v_v_1133_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; size_t v___x_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___x_1138_ = ((size_t)1ULL);
v___x_1139_ = lean_usize_add(v_i_1124_, v___x_1138_);
v___x_1140_ = lean_array_uset(v_bs_x27_1135_, v_i_1124_, v_a_1137_);
v_i_1124_ = v___x_1139_;
v_bs_1125_ = v___x_1140_;
goto _start;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec_ref(v_bs_x27_1135_);
v_a_1142_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1136_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1136_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object* v_sz_1150_, lean_object* v_i_1151_, lean_object* v_bs_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
size_t v_sz_boxed_1158_; size_t v_i_boxed_1159_; lean_object* v_res_1160_; 
v_sz_boxed_1158_ = lean_unbox_usize(v_sz_1150_);
lean_dec(v_sz_1150_);
v_i_boxed_1159_ = lean_unbox_usize(v_i_1151_);
lean_dec(v_i_1151_);
v_res_1160_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_boxed_1158_, v_i_boxed_1159_, v_bs_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(uint8_t v___x_1161_, lean_object* v_xs_1162_, lean_object* v_body_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
size_t v_sz_1172_; size_t v___x_1173_; lean_object* v___x_1174_; 
v_sz_1172_ = lean_array_size(v_xs_1162_);
v___x_1173_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1162_);
v___x_1174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1172_, v___x_1173_, v_xs_1162_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = l_Lean_Expr_replaceFVars(v_body_1163_, v_xs_1162_, v_a_1175_);
lean_dec(v_a_1175_);
v___x_1177_ = 0;
v___x_1178_ = 1;
v___x_1179_ = l_Lean_Meta_mkLambdaFVars(v_xs_1162_, v___x_1176_, v___x_1177_, v___x_1161_, v___x_1177_, v___x_1161_, v___x_1178_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_);
lean_dec_ref(v_xs_1162_);
return v___x_1179_;
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_xs_1162_);
v_a_1180_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1174_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1174_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_a_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0___boxed(lean_object* v___x_1188_, lean_object* v_xs_1189_, lean_object* v_body_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v___x_21965__boxed_1199_; lean_object* v_res_1200_; 
v___x_21965__boxed_1199_ = lean_unbox(v___x_1188_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(v___x_21965__boxed_1199_, v_xs_1189_, v_body_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v_body_1190_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t v_sz_1201_, size_t v_i_1202_, lean_object* v_bs_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_usize_dec_lt(v_i_1202_, v_sz_1201_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v_bs_1203_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v_v_1216_; lean_object* v___x_1217_; lean_object* v_bs_x27_1218_; uint8_t v___x_1219_; lean_object* v___x_1220_; 
v___x_1214_ = lean_box(v___x_1212_);
v___f_1215_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1215_, 0, v___x_1214_);
v_v_1216_ = lean_array_uget(v_bs_1203_, v_i_1202_);
v___x_1217_ = lean_unsigned_to_nat(0u);
v_bs_x27_1218_ = lean_array_uset(v_bs_1203_, v_i_1202_, v___x_1217_);
v___x_1219_ = 0;
v___x_1220_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_v_1216_, v___f_1215_, v___x_1219_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
if (lean_obj_tag(v___x_1220_) == 0)
{
lean_object* v_a_1221_; size_t v___x_1222_; size_t v___x_1223_; lean_object* v___x_1224_; 
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v___x_1220_, 1);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1202_, v___x_1222_);
v___x_1224_ = lean_array_uset(v_bs_x27_1218_, v_i_1202_, v_a_1221_);
v_i_1202_ = v___x_1223_;
v_bs_1203_ = v___x_1224_;
goto _start;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_bs_x27_1218_);
v_a_1226_ = lean_ctor_get(v___x_1220_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1220_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1220_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object* v_sz_1234_, lean_object* v_i_1235_, lean_object* v_bs_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
size_t v_sz_boxed_1245_; size_t v_i_boxed_1246_; lean_object* v_res_1247_; 
v_sz_boxed_1245_ = lean_unbox_usize(v_sz_1234_);
lean_dec(v_sz_1234_);
v_i_boxed_1246_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_boxed_1245_, v_i_boxed_1246_, v_bs_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
return v_res_1247_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object* v_as_1248_, size_t v_i_1249_, size_t v_stop_1250_){
_start:
{
uint8_t v___x_1251_; 
v___x_1251_ = lean_usize_dec_eq(v_i_1249_, v_stop_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = lean_array_uget_borrowed(v_as_1248_, v_i_1249_);
v___x_1253_ = l_Lean_Elab_WF_isWfParam_x3f(v___x_1252_);
if (lean_obj_tag(v___x_1253_) == 0)
{
size_t v___x_1254_; size_t v___x_1255_; 
v___x_1254_ = ((size_t)1ULL);
v___x_1255_ = lean_usize_add(v_i_1249_, v___x_1254_);
v_i_1249_ = v___x_1255_;
goto _start;
}
else
{
uint8_t v___x_1257_; 
lean_dec_ref_known(v___x_1253_, 1);
v___x_1257_ = 1;
return v___x_1257_;
}
}
else
{
uint8_t v___x_1258_; 
v___x_1258_ = 0;
return v___x_1258_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object* v_as_1259_, lean_object* v_i_1260_, lean_object* v_stop_1261_){
_start:
{
size_t v_i_boxed_1262_; size_t v_stop_boxed_1263_; uint8_t v_res_1264_; lean_object* v_r_1265_; 
v_i_boxed_1262_ = lean_unbox_usize(v_i_1260_);
lean_dec(v_i_1260_);
v_stop_boxed_1263_ = lean_unbox_usize(v_stop_1261_);
lean_dec(v_stop_1261_);
v_res_1264_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1259_, v_i_boxed_1262_, v_stop_boxed_1263_);
lean_dec_ref(v_as_1259_);
v_r_1265_ = lean_box(v_res_1264_);
return v_r_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher(lean_object* v_e_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
uint8_t v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = 1;
v___x_1276_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1266_, v___x_1275_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1339_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1339_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1339_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
if (lean_obj_tag(v_a_1277_) == 1)
{
lean_object* v_val_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1336_; 
v_val_1286_ = lean_ctor_get(v_a_1277_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_a_1277_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1288_ = v_a_1277_;
v_isShared_1289_ = v_isSharedCheck_1336_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_val_1286_);
lean_dec(v_a_1277_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1336_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_toMatcherInfo_1290_; lean_object* v_matcherName_1291_; lean_object* v_matcherLevels_1292_; lean_object* v_params_1293_; lean_object* v_motive_1294_; lean_object* v_discrs_1295_; lean_object* v_alts_1296_; lean_object* v_remaining_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1335_; 
v_toMatcherInfo_1290_ = lean_ctor_get(v_val_1286_, 0);
v_matcherName_1291_ = lean_ctor_get(v_val_1286_, 1);
v_matcherLevels_1292_ = lean_ctor_get(v_val_1286_, 2);
v_params_1293_ = lean_ctor_get(v_val_1286_, 3);
v_motive_1294_ = lean_ctor_get(v_val_1286_, 4);
v_discrs_1295_ = lean_ctor_get(v_val_1286_, 5);
v_alts_1296_ = lean_ctor_get(v_val_1286_, 6);
v_remaining_1297_ = lean_ctor_get(v_val_1286_, 7);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_val_1286_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1299_ = v_val_1286_;
v_isShared_1300_ = v_isSharedCheck_1335_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_remaining_1297_);
lean_inc(v_alts_1296_);
lean_inc(v_discrs_1295_);
lean_inc(v_motive_1294_);
lean_inc(v_params_1293_);
lean_inc(v_matcherLevels_1292_);
lean_inc(v_matcherName_1291_);
lean_inc(v_toMatcherInfo_1290_);
lean_dec(v_val_1286_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1335_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_get_size(v_discrs_1295_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_del_object(v___x_1299_);
lean_dec_ref(v_remaining_1297_);
lean_dec_ref(v_alts_1296_);
lean_dec_ref(v_discrs_1295_);
lean_dec_ref(v_motive_1294_);
lean_dec_ref(v_params_1293_);
lean_dec_ref(v_matcherLevels_1292_);
lean_dec(v_matcherName_1291_);
lean_dec_ref(v_toMatcherInfo_1290_);
lean_del_object(v___x_1288_);
goto v___jp_1281_;
}
else
{
if (v___x_1303_ == 0)
{
lean_del_object(v___x_1299_);
lean_dec_ref(v_remaining_1297_);
lean_dec_ref(v_alts_1296_);
lean_dec_ref(v_discrs_1295_);
lean_dec_ref(v_motive_1294_);
lean_dec_ref(v_params_1293_);
lean_dec_ref(v_matcherLevels_1292_);
lean_dec(v_matcherName_1291_);
lean_dec_ref(v_toMatcherInfo_1290_);
lean_del_object(v___x_1288_);
goto v___jp_1281_;
}
else
{
size_t v___x_1304_; size_t v___x_1305_; uint8_t v___x_1306_; 
v___x_1304_ = ((size_t)0ULL);
v___x_1305_ = lean_usize_of_nat(v___x_1302_);
v___x_1306_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_discrs_1295_, v___x_1304_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_del_object(v___x_1299_);
lean_dec_ref(v_remaining_1297_);
lean_dec_ref(v_alts_1296_);
lean_dec_ref(v_discrs_1295_);
lean_dec_ref(v_motive_1294_);
lean_dec_ref(v_params_1293_);
lean_dec_ref(v_matcherLevels_1292_);
lean_dec(v_matcherName_1291_);
lean_dec_ref(v_toMatcherInfo_1290_);
lean_del_object(v___x_1288_);
goto v___jp_1281_;
}
else
{
size_t v_sz_1307_; lean_object* v___x_1308_; size_t v_sz_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1279_);
v_sz_1307_ = lean_array_size(v_discrs_1295_);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_1307_, v___x_1304_, v_discrs_1295_);
v_sz_1309_ = lean_array_size(v_alts_1296_);
v___x_1310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1309_, v___x_1304_, v_alts_1296_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1326_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1313_ = v___x_1310_;
v_isShared_1314_ = v_isSharedCheck_1326_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1310_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1326_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 6, v_a_1311_);
lean_ctor_set(v___x_1299_, 5, v___x_1308_);
v___x_1316_ = v___x_1299_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_toMatcherInfo_1290_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v_matcherName_1291_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_matcherLevels_1292_);
lean_ctor_set(v_reuseFailAlloc_1325_, 3, v_params_1293_);
lean_ctor_set(v_reuseFailAlloc_1325_, 4, v_motive_1294_);
lean_ctor_set(v_reuseFailAlloc_1325_, 5, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1325_, 6, v_a_1311_);
lean_ctor_set(v_reuseFailAlloc_1325_, 7, v_remaining_1297_);
v___x_1316_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = l_Lean_Meta_MatcherApp_toExpr(v___x_1316_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1317_);
v___x_1319_ = v___x_1288_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1320_);
v___x_1322_ = v___x_1313_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_dec_ref(v___x_1308_);
lean_del_object(v___x_1299_);
lean_dec_ref(v_remaining_1297_);
lean_dec_ref(v_motive_1294_);
lean_dec_ref(v_params_1293_);
lean_dec_ref(v_matcherLevels_1292_);
lean_dec(v_matcherName_1291_);
lean_dec_ref(v_toMatcherInfo_1290_);
lean_del_object(v___x_1288_);
v_a_1327_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1310_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1310_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
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
lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_del_object(v___x_1279_);
lean_dec(v_a_1277_);
v___x_1337_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
return v___x_1338_;
}
v___jp_1281_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v___x_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1276_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1276_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object* v_e_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Elab_WF_paramMatcher(v_e_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t v_sz_1358_, size_t v_i_1359_, lean_object* v_bs_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1358_, v_i_1359_, v_bs_1360_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object* v_sz_1370_, lean_object* v_i_1371_, lean_object* v_bs_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
size_t v_sz_boxed_1381_; size_t v_i_boxed_1382_; lean_object* v_res_1383_; 
v_sz_boxed_1381_ = lean_unbox_usize(v_sz_1370_);
lean_dec(v_sz_1370_);
v_i_boxed_1382_ = lean_unbox_usize(v_i_1371_);
lean_dec(v_i_1371_);
v_res_1383_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_boxed_1381_, v_i_boxed_1382_, v_bs_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object* v_declName_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1384_, v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object* v_declName_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_1404_, lean_object* v_constName_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_constName_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(v_00_u03b1_1415_, v_constName_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b1_1426_, lean_object* v_ref_1427_, lean_object* v_constName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_1427_, v_constName_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b1_1438_, lean_object* v_ref_1439_, lean_object* v_constName_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(v_00_u03b1_1438_, v_ref_1439_, v_constName_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec(v_ref_1439_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_1450_, lean_object* v_ref_1451_, lean_object* v_msg_1452_, lean_object* v_declHint_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_1451_, v_msg_1452_, v_declHint_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1463_, lean_object* v_ref_1464_, lean_object* v_msg_1465_, lean_object* v_declHint_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_1463_, v_ref_1464_, v_msg_1465_, v_declHint_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec(v_ref_1464_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1476_, lean_object* v_declHint_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1476_, v_declHint_1477_, v___y_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1487_, lean_object* v_declHint_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1487_, v_declHint_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1498_, lean_object* v_ref_1499_, lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_1499_, v_msg_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_ref_1511_, lean_object* v_msg_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(v_00_u03b1_1510_, v_ref_1511_, v_msg_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec(v_ref_1511_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_1523_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1533_, lean_object* v_msg_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(v_00_u03b1_1533_, v_msg_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1551_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_));
v___x_1552_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1554_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1551_, v___x_1552_, v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10____boxed(lean_object* v_a_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_();
return v_res_1556_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object* v_e_1557_){
_start:
{
if (lean_obj_tag(v_e_1557_) == 8)
{
lean_object* v_value_1558_; lean_object* v_body_1559_; lean_object* v___x_1560_; 
v_value_1558_ = lean_ctor_get(v_e_1557_, 2);
v_body_1559_ = lean_ctor_get(v_e_1557_, 3);
v___x_1560_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1558_);
if (lean_obj_tag(v___x_1560_) == 0)
{
v_e_1557_ = v_body_1559_;
goto _start;
}
else
{
uint8_t v___x_1562_; 
lean_dec_ref_known(v___x_1560_, 1);
v___x_1562_ = 1;
return v___x_1562_;
}
}
else
{
uint8_t v___x_1563_; 
v___x_1563_ = 0;
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object* v_e_1564_){
_start:
{
uint8_t v_res_1565_; lean_object* v_r_1566_; 
v_res_1565_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1564_);
lean_dec_ref(v_e_1564_);
v_r_1566_ = lean_box(v_res_1565_);
return v_r_1566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object* v_e_1567_, lean_object* v_acc_1568_){
_start:
{
if (lean_obj_tag(v_e_1567_) == 8)
{
lean_object* v_value_1569_; lean_object* v_body_1570_; lean_object* v___x_1571_; 
v_value_1569_ = lean_ctor_get(v_e_1567_, 2);
v_body_1570_ = lean_ctor_get(v_e_1567_, 3);
v___x_1571_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1569_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_unsigned_to_nat(1u);
v___x_1573_ = lean_nat_add(v_acc_1568_, v___x_1572_);
lean_dec(v_acc_1568_);
v_e_1567_ = v_body_1570_;
v_acc_1568_ = v___x_1573_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1571_, 1);
return v_acc_1568_;
}
}
else
{
return v_acc_1568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object* v_e_1575_, lean_object* v_acc_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1575_, v_acc_1576_);
lean_dec_ref(v_e_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object* v_msg_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___f_1585_; lean_object* v___x_1085__overap_1586_; lean_object* v___x_1587_; 
v___f_1585_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0));
v___x_1085__overap_1586_ = lean_panic_fn_borrowed(v___f_1585_, v_msg_1579_);
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
v___x_1587_ = lean_apply_5(v___x_1085__overap_1586_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_, lean_box(0));
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object* v_msg_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object* v_k_1595_, lean_object* v_b_1596_, lean_object* v_c_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
lean_inc(v___y_1601_);
lean_inc_ref(v___y_1600_);
lean_inc(v___y_1599_);
lean_inc_ref(v___y_1598_);
v___x_1603_ = lean_apply_7(v_k_1595_, v_b_1596_, v_c_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, lean_box(0));
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object* v_k_1604_, lean_object* v_b_1605_, lean_object* v_c_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v_res_1612_; 
v_res_1612_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1604_, v_b_1605_, v_c_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
lean_dec(v___y_1610_);
lean_dec_ref(v___y_1609_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object* v_e_1613_, lean_object* v_maxFVars_x3f_1614_, lean_object* v_k_1615_, uint8_t v_cleanupAnnotations_1616_, uint8_t v_preserveNondepLet_1617_, uint8_t v_nondepLetOnly_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___f_1624_; uint8_t v___x_1625_; uint8_t v___x_1626_; lean_object* v___x_1627_; 
v___f_1624_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1624_, 0, v_k_1615_);
v___x_1625_ = 0;
v___x_1626_ = 1;
v___x_1627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1613_, v___x_1625_, v___x_1626_, v_preserveNondepLet_1617_, v_nondepLetOnly_1618_, v_maxFVars_x3f_1614_, v___f_1624_, v_cleanupAnnotations_1616_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1635_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1635_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1633_; 
if (v_isShared_1631_ == 0)
{
v___x_1633_ = v___x_1630_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1628_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
v_a_1636_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1627_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1627_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object* v_e_1644_, lean_object* v_maxFVars_x3f_1645_, lean_object* v_k_1646_, lean_object* v_cleanupAnnotations_1647_, lean_object* v_preserveNondepLet_1648_, lean_object* v_nondepLetOnly_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1655_; uint8_t v_preserveNondepLet_boxed_1656_; uint8_t v_nondepLetOnly_boxed_1657_; lean_object* v_res_1658_; 
v_cleanupAnnotations_boxed_1655_ = lean_unbox(v_cleanupAnnotations_1647_);
v_preserveNondepLet_boxed_1656_ = lean_unbox(v_preserveNondepLet_1648_);
v_nondepLetOnly_boxed_1657_ = lean_unbox(v_nondepLetOnly_1649_);
v_res_1658_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1644_, v_maxFVars_x3f_1645_, v_k_1646_, v_cleanupAnnotations_boxed_1655_, v_preserveNondepLet_boxed_1656_, v_nondepLetOnly_boxed_1657_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v_maxFVars_x3f_1645_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object* v_00_u03b1_1659_, lean_object* v_e_1660_, lean_object* v_maxFVars_x3f_1661_, lean_object* v_k_1662_, uint8_t v_cleanupAnnotations_1663_, uint8_t v_preserveNondepLet_1664_, uint8_t v_nondepLetOnly_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1660_, v_maxFVars_x3f_1661_, v_k_1662_, v_cleanupAnnotations_1663_, v_preserveNondepLet_1664_, v_nondepLetOnly_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_e_1673_, lean_object* v_maxFVars_x3f_1674_, lean_object* v_k_1675_, lean_object* v_cleanupAnnotations_1676_, lean_object* v_preserveNondepLet_1677_, lean_object* v_nondepLetOnly_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1684_; uint8_t v_preserveNondepLet_boxed_1685_; uint8_t v_nondepLetOnly_boxed_1686_; lean_object* v_res_1687_; 
v_cleanupAnnotations_boxed_1684_ = lean_unbox(v_cleanupAnnotations_1676_);
v_preserveNondepLet_boxed_1685_ = lean_unbox(v_preserveNondepLet_1677_);
v_nondepLetOnly_boxed_1686_ = lean_unbox(v_nondepLetOnly_1678_);
v_res_1687_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(v_00_u03b1_1672_, v_e_1673_, v_maxFVars_x3f_1674_, v_k_1675_, v_cleanupAnnotations_boxed_1684_, v_preserveNondepLet_boxed_1685_, v_nondepLetOnly_boxed_1686_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_maxFVars_x3f_1674_);
return v_res_1687_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = l_Lean_Expr_bvar___override(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1693_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3));
v___x_1694_ = lean_unsigned_to_nat(6u);
v___x_1695_ = lean_unsigned_to_nat(142u);
v___x_1696_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2));
v___x_1697_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1));
v___x_1698_ = l_mkPanicMessageWithDecl(v___x_1697_, v___x_1696_, v___x_1695_, v___x_1694_, v___x_1693_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object* v_xs_1699_, lean_object* v_b_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1699_, v_b_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec_ref(v_xs_1699_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object* v_e_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_){
_start:
{
if (lean_obj_tag(v_e_1707_) == 8)
{
lean_object* v_declName_1713_; lean_object* v_type_1714_; lean_object* v_value_1715_; lean_object* v_body_1716_; uint8_t v_nondep_1717_; lean_object* v___x_1718_; 
v_declName_1713_ = lean_ctor_get(v_e_1707_, 0);
v_type_1714_ = lean_ctor_get(v_e_1707_, 1);
v_value_1715_ = lean_ctor_get(v_e_1707_, 2);
v_body_1716_ = lean_ctor_get(v_e_1707_, 3);
v_nondep_1717_ = lean_ctor_get_uint8(v_e_1707_, sizeof(void*)*4 + 8);
v___x_1718_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1715_);
if (lean_obj_tag(v___x_1718_) == 1)
{
lean_object* v_val_1719_; lean_object* v___x_1720_; 
v_val_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1719_);
lean_dec_ref_known(v___x_1718_, 1);
lean_inc_ref(v_type_1714_);
v___x_1720_ = l_Lean_Meta_isProp(v_type_1714_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = lean_unbox(v_a_1721_);
lean_dec(v_a_1721_);
if (v___x_1722_ == 0)
{
lean_object* v___x_1723_; 
lean_inc_ref(v_type_1714_);
v___x_1723_ = l_Lean_Meta_getLevel(v_type_1714_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; size_t v___x_1732_; uint8_t v___x_1733_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_1726_ = lean_box(0);
v___x_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1727_, 0, v_a_1724_);
lean_ctor_set(v___x_1727_, 1, v___x_1726_);
v___x_1728_ = l_Lean_Expr_const___override(v___x_1725_, v___x_1727_);
v___x_1729_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0);
lean_inc_ref(v_type_1714_);
v___x_1730_ = l_Lean_mkAppB(v___x_1728_, v_type_1714_, v___x_1729_);
v___x_1731_ = lean_expr_instantiate1(v_body_1716_, v___x_1730_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = lean_ptr_addr(v_type_1714_);
v___x_1733_ = lean_usize_dec_eq(v___x_1732_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_inc_ref(v_type_1714_);
lean_inc(v_declName_1713_);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1734_ = l_Lean_Expr_letE___override(v_declName_1713_, v_type_1714_, v_val_1719_, v___x_1731_, v_nondep_1717_);
v_e_1707_ = v___x_1734_;
goto _start;
}
else
{
size_t v___x_1736_; size_t v___x_1737_; uint8_t v___x_1738_; 
v___x_1736_ = lean_ptr_addr(v_value_1715_);
v___x_1737_ = lean_ptr_addr(v_val_1719_);
v___x_1738_ = lean_usize_dec_eq(v___x_1736_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; 
lean_inc_ref(v_type_1714_);
lean_inc(v_declName_1713_);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1739_ = l_Lean_Expr_letE___override(v_declName_1713_, v_type_1714_, v_val_1719_, v___x_1731_, v_nondep_1717_);
v_e_1707_ = v___x_1739_;
goto _start;
}
else
{
size_t v___x_1741_; size_t v___x_1742_; uint8_t v___x_1743_; 
v___x_1741_ = lean_ptr_addr(v_body_1716_);
v___x_1742_ = lean_ptr_addr(v___x_1731_);
v___x_1743_ = lean_usize_dec_eq(v___x_1741_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_inc_ref(v_type_1714_);
lean_inc(v_declName_1713_);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1744_ = l_Lean_Expr_letE___override(v_declName_1713_, v_type_1714_, v_val_1719_, v___x_1731_, v_nondep_1717_);
v_e_1707_ = v___x_1744_;
goto _start;
}
else
{
lean_dec_ref(v___x_1731_);
lean_dec(v_val_1719_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_val_1719_);
lean_dec_ref_known(v_e_1707_, 4);
v_a_1747_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1723_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1723_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
size_t v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_ptr_addr(v_type_1714_);
v___x_1756_ = lean_usize_dec_eq(v___x_1755_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_inc_ref(v_body_1716_);
lean_inc_ref(v_type_1714_);
lean_inc(v_declName_1713_);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1757_ = l_Lean_Expr_letE___override(v_declName_1713_, v_type_1714_, v_val_1719_, v_body_1716_, v_nondep_1717_);
v_e_1707_ = v___x_1757_;
goto _start;
}
else
{
size_t v___x_1759_; size_t v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = lean_ptr_addr(v_value_1715_);
v___x_1760_ = lean_ptr_addr(v_val_1719_);
v___x_1761_ = lean_usize_dec_eq(v___x_1759_, v___x_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1762_; 
lean_inc_ref(v_body_1716_);
lean_inc_ref(v_type_1714_);
lean_inc(v_declName_1713_);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1762_ = l_Lean_Expr_letE___override(v_declName_1713_, v_type_1714_, v_val_1719_, v_body_1716_, v_nondep_1717_);
v_e_1707_ = v___x_1762_;
goto _start;
}
else
{
size_t v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = lean_ptr_addr(v_body_1716_);
v___x_1765_ = lean_usize_dec_eq(v___x_1764_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
lean_inc_ref(v_body_1716_);
lean_inc_ref(v_type_1714_);
lean_inc(v_declName_1713_);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1766_ = l_Lean_Expr_letE___override(v_declName_1713_, v_type_1714_, v_val_1719_, v_body_1716_, v_nondep_1717_);
v_e_1707_ = v___x_1766_;
goto _start;
}
else
{
lean_dec(v_val_1719_);
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_val_1719_);
lean_dec_ref_known(v_e_1707_, 4);
v_a_1769_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1720_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1720_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
else
{
lean_object* v___x_1777_; lean_object* v_num_1778_; uint8_t v___x_1779_; 
lean_dec(v___x_1718_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v_num_1778_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1707_, v___x_1777_);
v___x_1779_ = lean_nat_dec_lt(v___x_1777_, v_num_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
lean_dec(v_num_1778_);
lean_dec_ref_known(v_e_1707_, 4);
v___x_1780_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4);
v___x_1781_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v___x_1780_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
return v___x_1781_;
}
else
{
lean_object* v___f_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; lean_object* v___x_1785_; 
v___f_1782_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed), 7, 0);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_num_1778_);
v___x_1784_ = 0;
v___x_1785_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1707_, v___x_1783_, v___f_1782_, v___x_1784_, v___x_1779_, v___x_1784_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_);
lean_dec_ref_known(v___x_1783_, 1);
return v___x_1785_;
}
}
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_e_1707_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object* v_xs_1787_, lean_object* v_b_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_b_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; uint8_t v___x_1796_; uint8_t v___x_1797_; lean_object* v___x_1798_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref_known(v___x_1794_, 1);
v___x_1796_ = 0;
v___x_1797_ = 1;
v___x_1798_ = l_Lean_Meta_mkLetFVars(v_xs_1787_, v_a_1795_, v___x_1796_, v___x_1796_, v___x_1797_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1798_;
}
else
{
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object* v_e_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object* v_e_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_){
_start:
{
uint8_t v___x_1832_; 
v___x_1832_ = l_Lean_Expr_isLet(v_e_1806_);
if (v___x_1832_ == 0)
{
uint8_t v___x_1833_; 
v___x_1833_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1806_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
lean_dec_ref(v_e_1806_);
v___x_1834_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
return v___x_1835_;
}
else
{
goto v___jp_1812_;
}
}
else
{
goto v___jp_1812_;
}
v___jp_1812_:
{
lean_object* v___x_1813_; 
v___x_1813_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1823_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1823_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1818_, 0, v_a_1814_);
v___x_1819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1819_);
v___x_1821_ = v___x_1816_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1813_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1813_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object* v_e_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet(lean_object* v_e_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1843_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object* v_e_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_Elab_WF_paramLet(v_e_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1870_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_));
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_1872_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1873_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1870_, v___x_1871_, v___x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10____boxed(lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_();
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object* v_lctx_1876_, lean_object* v_x_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
lean_object* v_keyedConfig_1883_; uint8_t v_trackZetaDelta_1884_; lean_object* v_zetaDeltaSet_1885_; lean_object* v_localInstances_1886_; lean_object* v_defEqCtx_x3f_1887_; lean_object* v_synthPendingDepth_1888_; lean_object* v_customCanUnfoldPredicate_x3f_1889_; uint8_t v_univApprox_1890_; uint8_t v_inTypeClassResolution_1891_; uint8_t v_cacheInferType_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v_keyedConfig_1883_ = lean_ctor_get(v___y_1878_, 0);
v_trackZetaDelta_1884_ = lean_ctor_get_uint8(v___y_1878_, sizeof(void*)*7);
v_zetaDeltaSet_1885_ = lean_ctor_get(v___y_1878_, 1);
v_localInstances_1886_ = lean_ctor_get(v___y_1878_, 3);
v_defEqCtx_x3f_1887_ = lean_ctor_get(v___y_1878_, 4);
v_synthPendingDepth_1888_ = lean_ctor_get(v___y_1878_, 5);
v_customCanUnfoldPredicate_x3f_1889_ = lean_ctor_get(v___y_1878_, 6);
v_univApprox_1890_ = lean_ctor_get_uint8(v___y_1878_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1891_ = lean_ctor_get_uint8(v___y_1878_, sizeof(void*)*7 + 2);
v_cacheInferType_1892_ = lean_ctor_get_uint8(v___y_1878_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1889_);
lean_inc(v_synthPendingDepth_1888_);
lean_inc(v_defEqCtx_x3f_1887_);
lean_inc_ref(v_localInstances_1886_);
lean_inc(v_zetaDeltaSet_1885_);
lean_inc_ref(v_keyedConfig_1883_);
v___x_1893_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1893_, 0, v_keyedConfig_1883_);
lean_ctor_set(v___x_1893_, 1, v_zetaDeltaSet_1885_);
lean_ctor_set(v___x_1893_, 2, v_lctx_1876_);
lean_ctor_set(v___x_1893_, 3, v_localInstances_1886_);
lean_ctor_set(v___x_1893_, 4, v_defEqCtx_x3f_1887_);
lean_ctor_set(v___x_1893_, 5, v_synthPendingDepth_1888_);
lean_ctor_set(v___x_1893_, 6, v_customCanUnfoldPredicate_x3f_1889_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*7, v_trackZetaDelta_1884_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*7 + 1, v_univApprox_1890_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1891_);
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*7 + 3, v_cacheInferType_1892_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
lean_inc(v___y_1879_);
v___x_1894_ = lean_apply_5(v_x_1877_, v___x_1893_, v___y_1879_, v___y_1880_, v___y_1881_, lean_box(0));
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object* v_lctx_1895_, lean_object* v_x_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1895_, v_x_1896_, v___y_1897_, v___y_1898_, v___y_1899_, v___y_1900_);
lean_dec(v___y_1900_);
lean_dec_ref(v___y_1899_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object* v_00_u03b1_1903_, lean_object* v_lctx_1904_, lean_object* v_x_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1904_, v_x_1905_, v___y_1906_, v___y_1907_, v___y_1908_, v___y_1909_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object* v_00_u03b1_1912_, lean_object* v_lctx_1913_, lean_object* v_x_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v_res_1920_; 
v_res_1920_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(v_00_u03b1_1912_, v_lctx_1913_, v_x_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
lean_dec(v___y_1918_);
lean_dec_ref(v___y_1917_);
lean_dec(v___y_1916_);
lean_dec_ref(v___y_1915_);
return v_res_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object* v_e_1921_, lean_object* v_k_1922_, uint8_t v_cleanupAnnotations_1923_, uint8_t v_preserveNondepLet_1924_, uint8_t v_nondepLetOnly_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___f_1931_; uint8_t v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___f_1931_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1931_, 0, v_k_1922_);
v___x_1932_ = 0;
v___x_1933_ = 1;
v___x_1934_ = lean_box(0);
v___x_1935_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1921_, v___x_1932_, v___x_1933_, v_preserveNondepLet_1924_, v_nondepLetOnly_1925_, v___x_1934_, v___f_1931_, v_cleanupAnnotations_1923_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1943_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1943_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1941_; 
if (v_isShared_1939_ == 0)
{
v___x_1941_ = v___x_1938_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
v_a_1944_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1935_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1935_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object* v_e_1952_, lean_object* v_k_1953_, lean_object* v_cleanupAnnotations_1954_, lean_object* v_preserveNondepLet_1955_, lean_object* v_nondepLetOnly_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1962_; uint8_t v_preserveNondepLet_boxed_1963_; uint8_t v_nondepLetOnly_boxed_1964_; lean_object* v_res_1965_; 
v_cleanupAnnotations_boxed_1962_ = lean_unbox(v_cleanupAnnotations_1954_);
v_preserveNondepLet_boxed_1963_ = lean_unbox(v_preserveNondepLet_1955_);
v_nondepLetOnly_boxed_1964_ = lean_unbox(v_nondepLetOnly_1956_);
v_res_1965_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_1952_, v_k_1953_, v_cleanupAnnotations_boxed_1962_, v_preserveNondepLet_boxed_1963_, v_nondepLetOnly_boxed_1964_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object* v_00_u03b1_1966_, lean_object* v_e_1967_, lean_object* v_k_1968_, uint8_t v_cleanupAnnotations_1969_, uint8_t v_preserveNondepLet_1970_, uint8_t v_nondepLetOnly_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; 
v___x_1977_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_1967_, v_k_1968_, v_cleanupAnnotations_1969_, v_preserveNondepLet_1970_, v_nondepLetOnly_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object* v_00_u03b1_1978_, lean_object* v_e_1979_, lean_object* v_k_1980_, lean_object* v_cleanupAnnotations_1981_, lean_object* v_preserveNondepLet_1982_, lean_object* v_nondepLetOnly_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1989_; uint8_t v_preserveNondepLet_boxed_1990_; uint8_t v_nondepLetOnly_boxed_1991_; lean_object* v_res_1992_; 
v_cleanupAnnotations_boxed_1989_ = lean_unbox(v_cleanupAnnotations_1981_);
v_preserveNondepLet_boxed_1990_ = lean_unbox(v_preserveNondepLet_1982_);
v_nondepLetOnly_boxed_1991_ = lean_unbox(v_nondepLetOnly_1983_);
v_res_1992_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(v_00_u03b1_1978_, v_e_1979_, v_k_1980_, v_cleanupAnnotations_boxed_1989_, v_preserveNondepLet_boxed_1990_, v_nondepLetOnly_boxed_1991_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object* v_e_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_e_1993_);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object* v_e_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object* v_as_2008_, size_t v_i_2009_, size_t v_stop_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
uint8_t v___x_2017_; 
v___x_2017_ = lean_usize_dec_eq(v_i_2009_, v_stop_2010_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2018_ = lean_array_uget_borrowed(v_as_2008_, v_i_2009_);
v___x_2019_ = l_Lean_Expr_fvarId_x21(v___x_2018_);
v___x_2020_ = l_Lean_FVarId_getDecl___redArg(v___x_2019_, v___y_2012_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; uint8_t v_a_2023_; uint8_t v___x_2029_; 
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2029_ = l_Lean_LocalDecl_isNondep(v_a_2021_);
if (v___x_2029_ == 0)
{
v_a_2023_ = v___x_2029_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = l_Lean_LocalDecl_type(v_a_2021_);
v___x_2031_ = l_Lean_Meta_isProp(v___x_2030_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; uint8_t v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = lean_unbox(v_a_2032_);
lean_dec(v_a_2032_);
v_a_2023_ = v___x_2033_;
goto v___jp_2022_;
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_a_2021_);
lean_dec_ref(v_b_2011_);
v_a_2034_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2031_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2031_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
v___jp_2022_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; size_t v___x_2026_; size_t v___x_2027_; 
v___x_2024_ = l_Lean_LocalDecl_setNondep(v_a_2021_, v_a_2023_);
v___x_2025_ = l_Lean_LocalContext_addDecl(v_b_2011_, v___x_2024_);
v___x_2026_ = ((size_t)1ULL);
v___x_2027_ = lean_usize_add(v_i_2009_, v___x_2026_);
v_i_2009_ = v___x_2027_;
v_b_2011_ = v___x_2025_;
goto _start;
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v_b_2011_);
v_a_2042_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2020_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2020_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_b_2011_);
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object* v_as_2051_, lean_object* v_i_2052_, lean_object* v_stop_2053_, lean_object* v_b_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
size_t v_i_boxed_2060_; size_t v_stop_boxed_2061_; lean_object* v_res_2062_; 
v_i_boxed_2060_ = lean_unbox_usize(v_i_2052_);
lean_dec(v_i_2052_);
v_stop_boxed_2061_ = lean_unbox_usize(v_stop_2053_);
lean_dec(v_stop_2053_);
v_res_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2051_, v_i_boxed_2060_, v_stop_boxed_2061_, v_b_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
lean_dec_ref(v_as_2051_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t v_a_2063_, lean_object* v_lctx_2064_, lean_object* v_xs_2065_, lean_object* v_b_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_a_2073_; lean_object* v___x_2080_; lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = lean_array_get_size(v_xs_2065_);
v___x_2082_ = lean_nat_dec_lt(v___x_2080_, v___x_2081_);
if (v___x_2082_ == 0)
{
v_a_2073_ = v_lctx_2064_;
goto v___jp_2072_;
}
else
{
size_t v___x_2083_; size_t v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = ((size_t)0ULL);
v___x_2084_ = lean_usize_of_nat(v___x_2081_);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2065_, v___x_2083_, v___x_2084_, v_lctx_2064_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
v_a_2073_ = v_a_2086_;
goto v___jp_2072_;
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_dec_ref(v_b_2066_);
lean_dec_ref(v_xs_2065_);
v_a_2087_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2085_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2085_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
v___jp_2072_:
{
uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2074_ = 1;
v___x_2075_ = lean_box(v_a_2063_);
v___x_2076_ = lean_box(v_a_2063_);
v___x_2077_ = lean_box(v___x_2074_);
v___x_2078_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2078_, 0, v_xs_2065_);
lean_closure_set(v___x_2078_, 1, v_b_2066_);
lean_closure_set(v___x_2078_, 2, v___x_2075_);
lean_closure_set(v___x_2078_, 3, v___x_2076_);
lean_closure_set(v___x_2078_, 4, v___x_2077_);
v___x_2079_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_a_2073_, v___x_2078_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object* v_a_2095_, lean_object* v_lctx_2096_, lean_object* v_xs_2097_, lean_object* v_b_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
uint8_t v_a_11518__boxed_2104_; lean_object* v_res_2105_; 
v_a_11518__boxed_2104_ = lean_unbox(v_a_2095_);
v_res_2105_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_11518__boxed_2104_, v_lctx_2096_, v_xs_2097_, v_b_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object* v_e_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
lean_inc_ref(v_e_2106_);
v___x_2112_ = l_Lean_Meta_isProof(v_e_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2150_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2150_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2150_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
uint8_t v___x_2117_; 
v___x_2117_ = lean_unbox(v_a_2113_);
if (v___x_2117_ == 0)
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lean_Expr_isLet(v_e_2106_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
lean_dec(v_a_2113_);
lean_dec_ref(v_e_2106_);
v___x_2119_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2119_);
v___x_2121_ = v___x_2115_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
else
{
lean_object* v_lctx_2123_; lean_object* v___f_2124_; uint8_t v___x_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; 
lean_del_object(v___x_2115_);
v_lctx_2123_ = lean_ctor_get(v___y_2107_, 2);
lean_inc_ref(v_lctx_2123_);
lean_inc(v_a_2113_);
v___f_2124_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2124_, 0, v_a_2113_);
lean_closure_set(v___f_2124_, 1, v_lctx_2123_);
v___x_2125_ = lean_unbox(v_a_2113_);
v___x_2126_ = lean_unbox(v_a_2113_);
lean_dec(v_a_2113_);
v___x_2127_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2106_, v___f_2124_, v___x_2125_, v___x_2118_, v___x_2126_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2127_) == 0)
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2137_; 
v_a_2128_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2130_ = v___x_2127_;
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2127_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_a_2128_);
v___x_2133_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2133_);
v___x_2135_ = v___x_2130_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_a_2138_ = lean_ctor_get(v___x_2127_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2127_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2127_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_a_2113_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v_e_2106_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2146_);
v___x_2148_ = v___x_2115_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_e_2106_);
v_a_2151_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2112_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2112_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object* v_e_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object* v_00_u03b1_2166_, lean_object* v_x_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_apply_1(v_x_2167_, lean_box(0));
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_x_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(v_00_u03b1_2175_, v_x_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2182_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = l_Lean_maxRecDepthErrorMessage;
v___x_2189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3);
v___x_2191_ = l_Lean_MessageData_ofFormat(v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4);
v___x_2193_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2));
v___x_2194_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
lean_ctor_set(v___x_2194_, 1, v___x_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object* v_ref_2195_){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v_ref_2195_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object* v_ref_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2200_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object* v_x_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___y_2211_; lean_object* v_toCold_2220_; lean_object* v_currRecDepth_2221_; lean_object* v_ref_2222_; uint16_t v_optionFlags_2223_; uint8_t v_suppressElabErrors_2224_; uint8_t v_isRecordingDeps_2225_; lean_object* v_maxRecDepth_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v_toCold_2220_ = lean_ctor_get(v___y_2207_, 0);
v_currRecDepth_2221_ = lean_ctor_get(v___y_2207_, 1);
v_ref_2222_ = lean_ctor_get(v___y_2207_, 2);
v_optionFlags_2223_ = lean_ctor_get_uint16(v___y_2207_, sizeof(void*)*3);
v_suppressElabErrors_2224_ = lean_ctor_get_uint8(v___y_2207_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2225_ = lean_ctor_get_uint8(v___y_2207_, sizeof(void*)*3 + 3);
v_maxRecDepth_2231_ = lean_ctor_get(v_toCold_2220_, 3);
v___x_2232_ = lean_unsigned_to_nat(0u);
v___x_2233_ = lean_nat_dec_eq(v_maxRecDepth_2231_, v___x_2232_);
if (v___x_2233_ == 0)
{
uint8_t v___x_2234_; 
v___x_2234_ = lean_nat_dec_eq(v_currRecDepth_2221_, v_maxRecDepth_2231_);
if (v___x_2234_ == 0)
{
goto v___jp_2226_;
}
else
{
lean_object* v___x_2235_; 
lean_dec_ref(v_x_2203_);
lean_inc(v_ref_2222_);
v___x_2235_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2222_);
v___y_2211_ = v___x_2235_;
goto v___jp_2210_;
}
}
else
{
goto v___jp_2226_;
}
v___jp_2210_:
{
if (lean_obj_tag(v___y_2211_) == 0)
{
return v___y_2211_;
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
v_a_2212_ = lean_ctor_get(v___y_2211_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___y_2211_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___y_2211_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___y_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
v___jp_2226_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_nat_add(v_currRecDepth_2221_, v___x_2227_);
lean_inc(v_ref_2222_);
lean_inc_ref(v_toCold_2220_);
v___x_2229_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2229_, 0, v_toCold_2220_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
lean_ctor_set(v___x_2229_, 2, v_ref_2222_);
lean_ctor_set_uint16(v___x_2229_, sizeof(void*)*3, v_optionFlags_2223_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 2, v_suppressElabErrors_2224_);
lean_ctor_set_uint8(v___x_2229_, sizeof(void*)*3 + 3, v_isRecordingDeps_2225_);
lean_inc(v___y_2208_);
lean_inc(v___y_2206_);
lean_inc_ref(v___y_2205_);
lean_inc(v___y_2204_);
v___x_2230_ = lean_apply_6(v_x_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___x_2229_, v___y_2208_, lean_box(0));
v___y_2211_ = v___x_2230_;
goto v___jp_2210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2244_, lean_object* v___y_2245_, lean_object* v_b_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; 
lean_inc(v___y_2250_);
lean_inc_ref(v___y_2249_);
lean_inc(v___y_2248_);
lean_inc_ref(v___y_2247_);
lean_inc(v___y_2245_);
v___x_2252_ = lean_apply_7(v_k_2244_, v_b_2246_, v___y_2245_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, lean_box(0));
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2253_, lean_object* v___y_2254_, lean_object* v_b_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2253_, v___y_2254_, v_b_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2254_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2262_, uint8_t v_bi_2263_, lean_object* v_type_2264_, lean_object* v_k_2265_, uint8_t v_kind_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___f_2273_; lean_object* v___x_2274_; 
lean_inc(v___y_2267_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2273_, 0, v_k_2265_);
lean_closure_set(v___f_2273_, 1, v___y_2267_);
v___x_2274_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2262_, v_bi_2263_, v_type_2264_, v___f_2273_, v_kind_2266_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2274_) == 0)
{
return v___x_2274_;
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2283_, lean_object* v_bi_2284_, lean_object* v_type_2285_, lean_object* v_k_2286_, lean_object* v_kind_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
uint8_t v_bi_boxed_2294_; uint8_t v_kind_boxed_2295_; lean_object* v_res_2296_; 
v_bi_boxed_2294_ = lean_unbox(v_bi_2284_);
v_kind_boxed_2295_ = lean_unbox(v_kind_2287_);
v_res_2296_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2283_, v_bi_boxed_2294_, v_type_2285_, v_k_2286_, v_kind_boxed_2295_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__2(lean_object* v___x_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2297_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__2___boxed(lean_object* v___x_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__2(v___x_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2311_, lean_object* v_type_2312_, lean_object* v_val_2313_, lean_object* v_k_2314_, uint8_t v_nondep_2315_, uint8_t v_kind_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___f_2323_; lean_object* v___x_2324_; 
lean_inc(v___y_2317_);
v___f_2323_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2323_, 0, v_k_2314_);
lean_closure_set(v___f_2323_, 1, v___y_2317_);
v___x_2324_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2311_, v_type_2312_, v_val_2313_, v___f_2323_, v_nondep_2315_, v_kind_2316_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2324_) == 0)
{
return v___x_2324_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2333_, lean_object* v_type_2334_, lean_object* v_val_2335_, lean_object* v_k_2336_, lean_object* v_nondep_2337_, lean_object* v_kind_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
uint8_t v_nondep_boxed_2345_; uint8_t v_kind_boxed_2346_; lean_object* v_res_2347_; 
v_nondep_boxed_2345_ = lean_unbox(v_nondep_2337_);
v_kind_boxed_2346_ = lean_unbox(v_kind_2338_);
v_res_2347_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2333_, v_type_2334_, v_val_2335_, v_k_2336_, v_nondep_boxed_2345_, v_kind_boxed_2346_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_a_2348_, lean_object* v_x_2349_){
_start:
{
if (lean_obj_tag(v_x_2349_) == 0)
{
lean_object* v___x_2350_; 
v___x_2350_ = lean_box(0);
return v___x_2350_;
}
else
{
lean_object* v_key_2351_; lean_object* v_value_2352_; lean_object* v_tail_2353_; uint8_t v___x_2354_; 
v_key_2351_ = lean_ctor_get(v_x_2349_, 0);
v_value_2352_ = lean_ctor_get(v_x_2349_, 1);
v_tail_2353_ = lean_ctor_get(v_x_2349_, 2);
v___x_2354_ = l_Lean_ExprStructEq_beq(v_key_2351_, v_a_2348_);
if (v___x_2354_ == 0)
{
v_x_2349_ = v_tail_2353_;
goto _start;
}
else
{
lean_object* v___x_2356_; 
lean_inc(v_value_2352_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v_value_2352_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_a_2357_, lean_object* v_x_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___redArg(v_a_2357_, v_x_2358_);
lean_dec(v_x_2358_);
lean_dec_ref(v_a_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg(lean_object* v_m_2360_, lean_object* v_a_2361_){
_start:
{
lean_object* v_buckets_2362_; lean_object* v___x_2363_; uint64_t v___x_2364_; uint64_t v___x_2365_; uint64_t v___x_2366_; uint64_t v_fold_2367_; uint64_t v___x_2368_; uint64_t v___x_2369_; uint64_t v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; size_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v_buckets_2362_ = lean_ctor_get(v_m_2360_, 1);
v___x_2363_ = lean_array_get_size(v_buckets_2362_);
v___x_2364_ = l_Lean_ExprStructEq_hash(v_a_2361_);
v___x_2365_ = 32ULL;
v___x_2366_ = lean_uint64_shift_right(v___x_2364_, v___x_2365_);
v_fold_2367_ = lean_uint64_xor(v___x_2364_, v___x_2366_);
v___x_2368_ = 16ULL;
v___x_2369_ = lean_uint64_shift_right(v_fold_2367_, v___x_2368_);
v___x_2370_ = lean_uint64_xor(v_fold_2367_, v___x_2369_);
v___x_2371_ = lean_uint64_to_usize(v___x_2370_);
v___x_2372_ = lean_usize_of_nat(v___x_2363_);
v___x_2373_ = ((size_t)1ULL);
v___x_2374_ = lean_usize_sub(v___x_2372_, v___x_2373_);
v___x_2375_ = lean_usize_land(v___x_2371_, v___x_2374_);
v___x_2376_ = lean_array_uget_borrowed(v_buckets_2362_, v___x_2375_);
v___x_2377_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___redArg(v_a_2361_, v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_m_2378_, lean_object* v_a_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg(v_m_2378_, v_a_2379_);
lean_dec_ref(v_a_2379_);
lean_dec_ref(v_m_2378_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2381_, lean_object* v_x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_apply_1(v_x_2382_, lean_box(0));
v___x_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2390_, lean_object* v_x_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2390_, v_x_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
return v_res_2397_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2398_, lean_object* v_x_2399_){
_start:
{
if (lean_obj_tag(v_x_2399_) == 0)
{
uint8_t v___x_2400_; 
v___x_2400_ = 0;
return v___x_2400_;
}
else
{
lean_object* v_key_2401_; lean_object* v_tail_2402_; uint8_t v___x_2403_; 
v_key_2401_ = lean_ctor_get(v_x_2399_, 0);
v_tail_2402_ = lean_ctor_get(v_x_2399_, 2);
v___x_2403_ = l_Lean_ExprStructEq_beq(v_key_2401_, v_a_2398_);
if (v___x_2403_ == 0)
{
v_x_2399_ = v_tail_2402_;
goto _start;
}
else
{
return v___x_2403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2405_, lean_object* v_x_2406_){
_start:
{
uint8_t v_res_2407_; lean_object* v_r_2408_; 
v_res_2407_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2405_, v_x_2406_);
lean_dec(v_x_2406_);
lean_dec_ref(v_a_2405_);
v_r_2408_ = lean_box(v_res_2407_);
return v_r_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2409_, lean_object* v_b_2410_, lean_object* v_x_2411_){
_start:
{
if (lean_obj_tag(v_x_2411_) == 0)
{
lean_dec(v_b_2410_);
lean_dec_ref(v_a_2409_);
return v_x_2411_;
}
else
{
lean_object* v_key_2412_; lean_object* v_value_2413_; lean_object* v_tail_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2426_; 
v_key_2412_ = lean_ctor_get(v_x_2411_, 0);
v_value_2413_ = lean_ctor_get(v_x_2411_, 1);
v_tail_2414_ = lean_ctor_get(v_x_2411_, 2);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_x_2411_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2416_ = v_x_2411_;
v_isShared_2417_ = v_isSharedCheck_2426_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_tail_2414_);
lean_inc(v_value_2413_);
lean_inc(v_key_2412_);
lean_dec(v_x_2411_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2426_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
uint8_t v___x_2418_; 
v___x_2418_ = l_Lean_ExprStructEq_beq(v_key_2412_, v_a_2409_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2419_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2409_, v_b_2410_, v_tail_2414_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 2, v___x_2419_);
v___x_2421_ = v___x_2416_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_key_2412_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_value_2413_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
else
{
lean_object* v___x_2424_; 
lean_dec(v_value_2413_);
lean_dec(v_key_2412_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v_b_2410_);
lean_ctor_set(v___x_2416_, 0, v_a_2409_);
v___x_2424_ = v___x_2416_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2409_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_b_2410_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v_tail_2414_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2427_, lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 0)
{
return v_x_2427_;
}
else
{
lean_object* v_key_2429_; lean_object* v_value_2430_; lean_object* v_tail_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2454_; 
v_key_2429_ = lean_ctor_get(v_x_2428_, 0);
v_value_2430_ = lean_ctor_get(v_x_2428_, 1);
v_tail_2431_ = lean_ctor_get(v_x_2428_, 2);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2433_ = v_x_2428_;
v_isShared_2434_ = v_isSharedCheck_2454_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_tail_2431_);
lean_inc(v_value_2430_);
lean_inc(v_key_2429_);
lean_dec(v_x_2428_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2454_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; uint64_t v___x_2436_; uint64_t v___x_2437_; uint64_t v___x_2438_; uint64_t v_fold_2439_; uint64_t v___x_2440_; uint64_t v___x_2441_; uint64_t v___x_2442_; size_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2435_ = lean_array_get_size(v_x_2427_);
v___x_2436_ = l_Lean_ExprStructEq_hash(v_key_2429_);
v___x_2437_ = 32ULL;
v___x_2438_ = lean_uint64_shift_right(v___x_2436_, v___x_2437_);
v_fold_2439_ = lean_uint64_xor(v___x_2436_, v___x_2438_);
v___x_2440_ = 16ULL;
v___x_2441_ = lean_uint64_shift_right(v_fold_2439_, v___x_2440_);
v___x_2442_ = lean_uint64_xor(v_fold_2439_, v___x_2441_);
v___x_2443_ = lean_uint64_to_usize(v___x_2442_);
v___x_2444_ = lean_usize_of_nat(v___x_2435_);
v___x_2445_ = ((size_t)1ULL);
v___x_2446_ = lean_usize_sub(v___x_2444_, v___x_2445_);
v___x_2447_ = lean_usize_land(v___x_2443_, v___x_2446_);
v___x_2448_ = lean_array_uget_borrowed(v_x_2427_, v___x_2447_);
lean_inc(v___x_2448_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 2, v___x_2448_);
v___x_2450_ = v___x_2433_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_key_2429_);
lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_value_2430_);
lean_ctor_set(v_reuseFailAlloc_2453_, 2, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; 
v___x_2451_ = lean_array_uset(v_x_2427_, v___x_2447_, v___x_2450_);
v_x_2427_ = v___x_2451_;
v_x_2428_ = v_tail_2431_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2455_, lean_object* v_source_2456_, lean_object* v_target_2457_){
_start:
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = lean_array_get_size(v_source_2456_);
v___x_2459_ = lean_nat_dec_lt(v_i_2455_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_dec_ref(v_source_2456_);
lean_dec(v_i_2455_);
return v_target_2457_;
}
else
{
lean_object* v_es_2460_; lean_object* v___x_2461_; lean_object* v_source_2462_; lean_object* v_target_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_es_2460_ = lean_array_fget(v_source_2456_, v_i_2455_);
v___x_2461_ = lean_box(0);
v_source_2462_ = lean_array_fset(v_source_2456_, v_i_2455_, v___x_2461_);
v_target_2463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2457_, v_es_2460_);
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2465_ = lean_nat_add(v_i_2455_, v___x_2464_);
lean_dec(v_i_2455_);
v_i_2455_ = v___x_2465_;
v_source_2456_ = v_source_2462_;
v_target_2457_ = v_target_2463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2467_){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_nbuckets_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2468_ = lean_array_get_size(v_data_2467_);
v___x_2469_ = lean_unsigned_to_nat(2u);
v_nbuckets_2470_ = lean_nat_mul(v___x_2468_, v___x_2469_);
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_mk_array(v_nbuckets_2470_, v___x_2472_);
v___x_2474_ = lean_array_propagate_mark(v_data_2467_, v___x_2473_);
v___x_2475_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2471_, v_data_2467_, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2476_, lean_object* v_a_2477_, lean_object* v_b_2478_){
_start:
{
lean_object* v_size_2479_; lean_object* v_buckets_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2523_; 
v_size_2479_ = lean_ctor_get(v_m_2476_, 0);
v_buckets_2480_ = lean_ctor_get(v_m_2476_, 1);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_m_2476_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2482_ = v_m_2476_;
v_isShared_2483_ = v_isSharedCheck_2523_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_buckets_2480_);
lean_inc(v_size_2479_);
lean_dec(v_m_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2523_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; uint64_t v___x_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v_fold_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; lean_object* v_bkt_2497_; uint8_t v___x_2498_; 
v___x_2484_ = lean_array_get_size(v_buckets_2480_);
v___x_2485_ = l_Lean_ExprStructEq_hash(v_a_2477_);
v___x_2486_ = 32ULL;
v___x_2487_ = lean_uint64_shift_right(v___x_2485_, v___x_2486_);
v_fold_2488_ = lean_uint64_xor(v___x_2485_, v___x_2487_);
v___x_2489_ = 16ULL;
v___x_2490_ = lean_uint64_shift_right(v_fold_2488_, v___x_2489_);
v___x_2491_ = lean_uint64_xor(v_fold_2488_, v___x_2490_);
v___x_2492_ = lean_uint64_to_usize(v___x_2491_);
v___x_2493_ = lean_usize_of_nat(v___x_2484_);
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_sub(v___x_2493_, v___x_2494_);
v___x_2496_ = lean_usize_land(v___x_2492_, v___x_2495_);
v_bkt_2497_ = lean_array_uget_borrowed(v_buckets_2480_, v___x_2496_);
v___x_2498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2477_, v_bkt_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2499_; lean_object* v_size_x27_2500_; lean_object* v___x_2501_; lean_object* v_buckets_x27_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2499_ = lean_unsigned_to_nat(1u);
v_size_x27_2500_ = lean_nat_add(v_size_2479_, v___x_2499_);
lean_dec(v_size_2479_);
lean_inc(v_bkt_2497_);
v___x_2501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2477_);
lean_ctor_set(v___x_2501_, 1, v_b_2478_);
lean_ctor_set(v___x_2501_, 2, v_bkt_2497_);
v_buckets_x27_2502_ = lean_array_uset(v_buckets_2480_, v___x_2496_, v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(4u);
v___x_2504_ = lean_nat_mul(v_size_x27_2500_, v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(3u);
v___x_2506_ = lean_nat_div(v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_array_get_size(v_buckets_x27_2502_);
v___x_2508_ = lean_nat_dec_le(v___x_2506_, v___x_2507_);
lean_dec(v___x_2506_);
if (v___x_2508_ == 0)
{
lean_object* v_val_2509_; lean_object* v___x_2511_; 
v_val_2509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2502_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_val_2509_);
lean_ctor_set(v___x_2482_, 0, v_size_x27_2500_);
v___x_2511_ = v___x_2482_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_size_x27_2500_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_val_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
else
{
lean_object* v___x_2514_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v_buckets_x27_2502_);
lean_ctor_set(v___x_2482_, 0, v_size_x27_2500_);
v___x_2514_ = v___x_2482_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_size_x27_2500_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_buckets_x27_2502_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
else
{
lean_object* v___x_2516_; lean_object* v_buckets_x27_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_inc(v_bkt_2497_);
v___x_2516_ = lean_box(0);
v_buckets_x27_2517_ = lean_array_uset(v_buckets_2480_, v___x_2496_, v___x_2516_);
v___x_2518_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2477_, v_b_2478_, v_bkt_2497_);
v___x_2519_ = lean_array_uset(v_buckets_x27_2517_, v___x_2496_, v___x_2518_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2519_);
v___x_2521_ = v___x_2482_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_size_2479_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2524_, lean_object* v_e_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2528_ = lean_st_ref_take(v_a_2524_);
v___x_2529_ = lean_box(0);
v___x_2530_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2528_, v_e_2525_, v_a_2526_);
v___x_2531_ = lean_st_ref_put(v_a_2524_, v___x_2530_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2532_, lean_object* v_e_2533_, lean_object* v_a_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2532_, v_e_2533_, v_a_2534_);
lean_dec(v_a_2532_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_2537_, lean_object* v_pre_2538_, lean_object* v_post_2539_, lean_object* v_usedLetOnly_2540_, lean_object* v_skipConstInApp_2541_, lean_object* v_skipInstances_2542_, lean_object* v_postApp_2543_, lean_object* v_body_2544_, lean_object* v_x_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
uint8_t v_usedLetOnly_boxed_2552_; uint8_t v_skipConstInApp_boxed_2553_; uint8_t v_skipInstances_boxed_2554_; lean_object* v_res_2555_; 
v_usedLetOnly_boxed_2552_ = lean_unbox(v_usedLetOnly_2540_);
v_skipConstInApp_boxed_2553_ = lean_unbox(v_skipConstInApp_2541_);
v_skipInstances_boxed_2554_ = lean_unbox(v_skipInstances_2542_);
v_res_2555_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_2537_, v_pre_2538_, v_post_2539_, v_usedLetOnly_boxed_2552_, v_skipConstInApp_boxed_2553_, v_skipInstances_boxed_2554_, v_postApp_2543_, v_body_2544_, v_x_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2559_, lean_object* v_pre_2560_, lean_object* v_post_2561_, uint8_t v_usedLetOnly_2562_, uint8_t v_skipConstInApp_2563_, uint8_t v_skipInstances_2564_, lean_object* v_postApp_2565_, lean_object* v_body_2566_, lean_object* v_x_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_array_push(v_fvars_2559_, v_x_2567_);
v___x_2575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2560_, v_post_2561_, v_usedLetOnly_2562_, v_skipConstInApp_2563_, v_skipInstances_2564_, v_postApp_2565_, v___x_2574_, v_body_2566_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2576_, lean_object* v_pre_2577_, lean_object* v_post_2578_, lean_object* v_usedLetOnly_2579_, lean_object* v_skipConstInApp_2580_, lean_object* v_skipInstances_2581_, lean_object* v_postApp_2582_, lean_object* v_body_2583_, lean_object* v_x_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v_usedLetOnly_boxed_2591_; uint8_t v_skipConstInApp_boxed_2592_; uint8_t v_skipInstances_boxed_2593_; lean_object* v_res_2594_; 
v_usedLetOnly_boxed_2591_ = lean_unbox(v_usedLetOnly_2579_);
v_skipConstInApp_boxed_2592_ = lean_unbox(v_skipConstInApp_2580_);
v_skipInstances_boxed_2593_ = lean_unbox(v_skipInstances_2581_);
v_res_2594_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2576_, v_pre_2577_, v_post_2578_, v_usedLetOnly_boxed_2591_, v_skipConstInApp_boxed_2592_, v_skipInstances_boxed_2593_, v_postApp_2582_, v_body_2583_, v_x_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_pre_2595_, lean_object* v_post_2596_, uint8_t v_usedLetOnly_2597_, uint8_t v_skipConstInApp_2598_, uint8_t v_skipInstances_2599_, lean_object* v_postApp_2600_, lean_object* v_e_2601_, lean_object* v_a_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
lean_inc_ref(v_post_2596_);
lean_inc(v___y_2606_);
lean_inc_ref(v___y_2605_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc_ref(v_e_2601_);
v___x_2608_ = lean_apply_6(v_post_2596_, v_e_2601_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, lean_box(0));
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2627_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2611_ = v___x_2608_;
v_isShared_2612_ = v_isSharedCheck_2627_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2627_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
switch(lean_obj_tag(v_a_2609_))
{
case 0:
{
lean_object* v_e_2613_; lean_object* v___x_2615_; 
lean_dec_ref(v_e_2601_);
lean_dec_ref(v_postApp_2600_);
lean_dec_ref(v_post_2596_);
lean_dec_ref(v_pre_2595_);
v_e_2613_ = lean_ctor_get(v_a_2609_, 0);
lean_inc_ref(v_e_2613_);
lean_dec_ref_known(v_a_2609_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_e_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_e_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
case 1:
{
lean_object* v_e_2617_; lean_object* v___x_2618_; 
lean_del_object(v___x_2611_);
lean_dec_ref(v_e_2601_);
v_e_2617_ = lean_ctor_get(v_a_2609_, 0);
lean_inc_ref(v_e_2617_);
lean_dec_ref_known(v_a_2609_, 1);
v___x_2618_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2595_, v_post_2596_, v_usedLetOnly_2597_, v_skipConstInApp_2598_, v_skipInstances_2599_, v_postApp_2600_, v_e_2617_, v_a_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
return v___x_2618_;
}
default: 
{
lean_object* v_e_x3f_2619_; 
lean_dec_ref(v_postApp_2600_);
lean_dec_ref(v_post_2596_);
lean_dec_ref(v_pre_2595_);
v_e_x3f_2619_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_e_x3f_2619_);
lean_dec_ref_known(v_a_2609_, 1);
if (lean_obj_tag(v_e_x3f_2619_) == 0)
{
lean_object* v___x_2621_; 
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_e_2601_);
v___x_2621_ = v___x_2611_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_e_2601_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v_val_2623_; lean_object* v___x_2625_; 
lean_dec_ref(v_e_2601_);
v_val_2623_ = lean_ctor_get(v_e_x3f_2619_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v_e_x3f_2619_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_val_2623_);
v___x_2625_ = v___x_2611_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_val_2623_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
}
else
{
lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2635_; 
lean_dec_ref(v_e_2601_);
lean_dec_ref(v_postApp_2600_);
lean_dec_ref(v_post_2596_);
lean_dec_ref(v_pre_2595_);
v_a_2628_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2630_ = v___x_2608_;
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_dec(v___x_2608_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2635_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2633_; 
if (v_isShared_2631_ == 0)
{
v___x_2633_ = v___x_2630_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v_a_2628_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2636_, lean_object* v_post_2637_, uint8_t v_usedLetOnly_2638_, uint8_t v_skipConstInApp_2639_, uint8_t v_skipInstances_2640_, lean_object* v_postApp_2641_, lean_object* v_fvars_2642_, lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
if (lean_obj_tag(v_e_2643_) == 6)
{
lean_object* v_binderName_2650_; lean_object* v_binderType_2651_; lean_object* v_body_2652_; uint8_t v_binderInfo_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___f_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_binderName_2650_ = lean_ctor_get(v_e_2643_, 0);
lean_inc(v_binderName_2650_);
v_binderType_2651_ = lean_ctor_get(v_e_2643_, 1);
lean_inc_ref(v_binderType_2651_);
v_body_2652_ = lean_ctor_get(v_e_2643_, 2);
lean_inc_ref(v_body_2652_);
v_binderInfo_2653_ = lean_ctor_get_uint8(v_e_2643_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2643_, 3);
v___x_2654_ = lean_box(v_usedLetOnly_2638_);
v___x_2655_ = lean_box(v_skipConstInApp_2639_);
v___x_2656_ = lean_box(v_skipInstances_2640_);
lean_inc_ref(v_postApp_2641_);
lean_inc_ref(v_post_2637_);
lean_inc_ref(v_pre_2636_);
lean_inc_ref(v_fvars_2642_);
v___f_2657_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2657_, 0, v_fvars_2642_);
lean_closure_set(v___f_2657_, 1, v_pre_2636_);
lean_closure_set(v___f_2657_, 2, v_post_2637_);
lean_closure_set(v___f_2657_, 3, v___x_2654_);
lean_closure_set(v___f_2657_, 4, v___x_2655_);
lean_closure_set(v___f_2657_, 5, v___x_2656_);
lean_closure_set(v___f_2657_, 6, v_postApp_2641_);
lean_closure_set(v___f_2657_, 7, v_body_2652_);
v___x_2658_ = lean_expr_instantiate_rev(v_binderType_2651_, v_fvars_2642_);
lean_dec_ref(v_fvars_2642_);
lean_dec_ref(v_binderType_2651_);
v___x_2659_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2636_, v_post_2637_, v_usedLetOnly_2638_, v_skipConstInApp_2639_, v_skipInstances_2640_, v_postApp_2641_, v___x_2658_, v_a_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = 0;
v___x_2662_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2650_, v_binderInfo_2653_, v_a_2660_, v___f_2657_, v___x_2661_, v_a_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
return v___x_2662_;
}
else
{
lean_dec_ref(v___f_2657_);
lean_dec(v_binderName_2650_);
return v___x_2659_;
}
}
else
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_expr_instantiate_rev(v_e_2643_, v_fvars_2642_);
lean_dec_ref(v_e_2643_);
lean_inc_ref(v_postApp_2641_);
lean_inc_ref(v_post_2637_);
lean_inc_ref(v_pre_2636_);
v___x_2664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2636_, v_post_2637_, v_usedLetOnly_2638_, v_skipConstInApp_2639_, v_skipInstances_2640_, v_postApp_2641_, v___x_2663_, v_a_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; uint8_t v___x_2666_; uint8_t v___x_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = 0;
v___x_2667_ = 1;
v___x_2668_ = 1;
v___x_2669_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2642_, v_a_2665_, v___x_2666_, v_usedLetOnly_2638_, v___x_2666_, v___x_2667_, v___x_2668_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec_ref(v_fvars_2642_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2636_, v_post_2637_, v_usedLetOnly_2638_, v_skipConstInApp_2639_, v_skipInstances_2640_, v_postApp_2641_, v_a_2670_, v_a_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
return v___x_2671_;
}
else
{
lean_dec_ref(v_postApp_2641_);
lean_dec_ref(v_post_2637_);
lean_dec_ref(v_pre_2636_);
return v___x_2669_;
}
}
else
{
lean_dec_ref(v_fvars_2642_);
lean_dec_ref(v_postApp_2641_);
lean_dec_ref(v_post_2637_);
lean_dec_ref(v_pre_2636_);
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2672_, lean_object* v_pre_2673_, lean_object* v_post_2674_, uint8_t v_usedLetOnly_2675_, uint8_t v_skipConstInApp_2676_, uint8_t v_skipInstances_2677_, lean_object* v_postApp_2678_, lean_object* v_body_2679_, lean_object* v_x_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_array_push(v_fvars_2672_, v_x_2680_);
v___x_2688_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2673_, v_post_2674_, v_usedLetOnly_2675_, v_skipConstInApp_2676_, v_skipInstances_2677_, v_postApp_2678_, v___x_2687_, v_body_2679_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2689_, lean_object* v_pre_2690_, lean_object* v_post_2691_, lean_object* v_usedLetOnly_2692_, lean_object* v_skipConstInApp_2693_, lean_object* v_skipInstances_2694_, lean_object* v_postApp_2695_, lean_object* v_body_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
uint8_t v_usedLetOnly_boxed_2704_; uint8_t v_skipConstInApp_boxed_2705_; uint8_t v_skipInstances_boxed_2706_; lean_object* v_res_2707_; 
v_usedLetOnly_boxed_2704_ = lean_unbox(v_usedLetOnly_2692_);
v_skipConstInApp_boxed_2705_ = lean_unbox(v_skipConstInApp_2693_);
v_skipInstances_boxed_2706_ = lean_unbox(v_skipInstances_2694_);
v_res_2707_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2689_, v_pre_2690_, v_post_2691_, v_usedLetOnly_boxed_2704_, v_skipConstInApp_boxed_2705_, v_skipInstances_boxed_2706_, v_postApp_2695_, v_body_2696_, v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v___y_2700_);
lean_dec_ref(v___y_2699_);
lean_dec(v___y_2698_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2708_, lean_object* v_post_2709_, uint8_t v_usedLetOnly_2710_, uint8_t v_skipConstInApp_2711_, uint8_t v_skipInstances_2712_, lean_object* v_postApp_2713_, lean_object* v_fvars_2714_, lean_object* v_e_2715_, lean_object* v_a_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
if (lean_obj_tag(v_e_2715_) == 8)
{
lean_object* v_declName_2722_; lean_object* v_type_2723_; lean_object* v_value_2724_; lean_object* v_body_2725_; uint8_t v_nondep_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___f_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v_declName_2722_ = lean_ctor_get(v_e_2715_, 0);
lean_inc(v_declName_2722_);
v_type_2723_ = lean_ctor_get(v_e_2715_, 1);
lean_inc_ref(v_type_2723_);
v_value_2724_ = lean_ctor_get(v_e_2715_, 2);
lean_inc_ref(v_value_2724_);
v_body_2725_ = lean_ctor_get(v_e_2715_, 3);
lean_inc_ref(v_body_2725_);
v_nondep_2726_ = lean_ctor_get_uint8(v_e_2715_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2715_, 4);
v___x_2727_ = lean_box(v_usedLetOnly_2710_);
v___x_2728_ = lean_box(v_skipConstInApp_2711_);
v___x_2729_ = lean_box(v_skipInstances_2712_);
lean_inc_ref_n(v_postApp_2713_, 2);
lean_inc_ref_n(v_post_2709_, 2);
lean_inc_ref_n(v_pre_2708_, 2);
lean_inc_ref(v_fvars_2714_);
v___f_2730_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2730_, 0, v_fvars_2714_);
lean_closure_set(v___f_2730_, 1, v_pre_2708_);
lean_closure_set(v___f_2730_, 2, v_post_2709_);
lean_closure_set(v___f_2730_, 3, v___x_2727_);
lean_closure_set(v___f_2730_, 4, v___x_2728_);
lean_closure_set(v___f_2730_, 5, v___x_2729_);
lean_closure_set(v___f_2730_, 6, v_postApp_2713_);
lean_closure_set(v___f_2730_, 7, v_body_2725_);
v___x_2731_ = lean_expr_instantiate_rev(v_type_2723_, v_fvars_2714_);
lean_dec_ref(v_type_2723_);
v___x_2732_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2708_, v_post_2709_, v_usedLetOnly_2710_, v_skipConstInApp_2711_, v_skipInstances_2712_, v_postApp_2713_, v___x_2731_, v_a_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
v___x_2734_ = lean_expr_instantiate_rev(v_value_2724_, v_fvars_2714_);
lean_dec_ref(v_fvars_2714_);
lean_dec_ref(v_value_2724_);
v___x_2735_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2708_, v_post_2709_, v_usedLetOnly_2710_, v_skipConstInApp_2711_, v_skipInstances_2712_, v_postApp_2713_, v___x_2734_, v_a_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = 0;
v___x_2738_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2722_, v_a_2733_, v_a_2736_, v___f_2730_, v_nondep_2726_, v___x_2737_, v_a_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v___x_2738_;
}
else
{
lean_dec(v_a_2733_);
lean_dec_ref(v___f_2730_);
lean_dec(v_declName_2722_);
return v___x_2735_;
}
}
else
{
lean_dec_ref(v___f_2730_);
lean_dec_ref(v_value_2724_);
lean_dec(v_declName_2722_);
lean_dec_ref(v_fvars_2714_);
lean_dec_ref(v_postApp_2713_);
lean_dec_ref(v_post_2709_);
lean_dec_ref(v_pre_2708_);
return v___x_2732_;
}
}
else
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_expr_instantiate_rev(v_e_2715_, v_fvars_2714_);
lean_dec_ref(v_e_2715_);
lean_inc_ref(v_postApp_2713_);
lean_inc_ref(v_post_2709_);
lean_inc_ref(v_pre_2708_);
v___x_2740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2708_, v_post_2709_, v_usedLetOnly_2710_, v_skipConstInApp_2711_, v_skipInstances_2712_, v_postApp_2713_, v___x_2739_, v_a_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; uint8_t v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___x_2742_ = 0;
v___x_2743_ = 1;
v___x_2744_ = l_Lean_Meta_mkLetFVars(v_fvars_2714_, v_a_2741_, v_usedLetOnly_2710_, v___x_2742_, v___x_2743_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec_ref(v_fvars_2714_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2744_, 1);
v___x_2746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2708_, v_post_2709_, v_usedLetOnly_2710_, v_skipConstInApp_2711_, v_skipInstances_2712_, v_postApp_2713_, v_a_2745_, v_a_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
return v___x_2746_;
}
else
{
lean_dec_ref(v_postApp_2713_);
lean_dec_ref(v_post_2709_);
lean_dec_ref(v_pre_2708_);
return v___x_2744_;
}
}
else
{
lean_dec_ref(v_fvars_2714_);
lean_dec_ref(v_postApp_2713_);
lean_dec_ref(v_post_2709_);
lean_dec_ref(v_pre_2708_);
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2747_, lean_object* v_post_2748_, uint8_t v_usedLetOnly_2749_, uint8_t v_skipConstInApp_2750_, uint8_t v_skipInstances_2751_, lean_object* v_postApp_2752_, size_t v_sz_2753_, size_t v_i_2754_, lean_object* v_bs_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
uint8_t v___x_2762_; 
v___x_2762_ = lean_usize_dec_lt(v_i_2754_, v_sz_2753_);
if (v___x_2762_ == 0)
{
lean_object* v___x_2763_; 
lean_dec_ref(v_postApp_2752_);
lean_dec_ref(v_post_2748_);
lean_dec_ref(v_pre_2747_);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_bs_2755_);
return v___x_2763_;
}
else
{
lean_object* v_v_2764_; lean_object* v___x_2765_; lean_object* v_bs_x27_2766_; lean_object* v___x_2767_; 
v_v_2764_ = lean_array_uget(v_bs_2755_, v_i_2754_);
v___x_2765_ = lean_unsigned_to_nat(0u);
v_bs_x27_2766_ = lean_array_uset(v_bs_2755_, v_i_2754_, v___x_2765_);
lean_inc_ref(v_postApp_2752_);
lean_inc_ref(v_post_2748_);
lean_inc_ref(v_pre_2747_);
v___x_2767_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2747_, v_post_2748_, v_usedLetOnly_2749_, v_skipConstInApp_2750_, v_skipInstances_2751_, v_postApp_2752_, v_v_2764_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; size_t v___x_2769_; size_t v___x_2770_; lean_object* v___x_2771_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___x_2769_ = ((size_t)1ULL);
v___x_2770_ = lean_usize_add(v_i_2754_, v___x_2769_);
v___x_2771_ = lean_array_uset(v_bs_x27_2766_, v_i_2754_, v_a_2768_);
v_i_2754_ = v___x_2770_;
v_bs_2755_ = v___x_2771_;
goto _start;
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_bs_x27_2766_);
lean_dec_ref(v_postApp_2752_);
lean_dec_ref(v_post_2748_);
lean_dec_ref(v_pre_2747_);
v_a_2773_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2767_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2767_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__0(lean_object* v_pre_2781_, lean_object* v_post_2782_, uint8_t v_usedLetOnly_2783_, uint8_t v_skipConstInApp_2784_, uint8_t v_skipInstances_2785_, lean_object* v_postApp_2786_, lean_object* v___x_2787_, lean_object* v___y_2788_, lean_object* v_b_2789_, lean_object* v_a_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2781_, v_post_2782_, v_usedLetOnly_2783_, v_skipConstInApp_2784_, v_skipInstances_2785_, v_postApp_2786_, v___x_2787_, v___y_2788_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2806_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2799_ = v___x_2796_;
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v___x_2796_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2801_ = lean_array_fset(v_b_2789_, v_a_2790_, v_a_2797_);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2802_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref(v_b_2789_);
v_a_2807_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2814_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2814_ == 0)
{
v___x_2809_ = v___x_2796_;
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_a_2807_);
lean_dec(v___x_2796_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2814_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2807_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v_pre_2815_, lean_object* v_post_2816_, lean_object* v_usedLetOnly_2817_, lean_object* v_skipConstInApp_2818_, lean_object* v_skipInstances_2819_, lean_object* v_postApp_2820_, lean_object* v___x_2821_, lean_object* v___y_2822_, lean_object* v_b_2823_, lean_object* v_a_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v_usedLetOnly_boxed_2830_; uint8_t v_skipConstInApp_boxed_2831_; uint8_t v_skipInstances_boxed_2832_; lean_object* v_res_2833_; 
v_usedLetOnly_boxed_2830_ = lean_unbox(v_usedLetOnly_2817_);
v_skipConstInApp_boxed_2831_ = lean_unbox(v_skipConstInApp_2818_);
v_skipInstances_boxed_2832_ = lean_unbox(v_skipInstances_2819_);
v_res_2833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__0(v_pre_2815_, v_post_2816_, v_usedLetOnly_boxed_2830_, v_skipConstInApp_boxed_2831_, v_skipInstances_boxed_2832_, v_postApp_2820_, v___x_2821_, v___y_2822_, v_b_2823_, v_a_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v_a_2824_);
lean_dec(v___y_2822_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_upperBound_2834_, lean_object* v___x_2835_, lean_object* v_pre_2836_, lean_object* v_post_2837_, uint8_t v_usedLetOnly_2838_, uint8_t v_skipConstInApp_2839_, uint8_t v_skipInstances_2840_, lean_object* v_postApp_2841_, lean_object* v_a_2842_, lean_object* v_b_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___y_2851_; uint8_t v___x_2874_; 
v___x_2874_ = lean_nat_dec_lt(v_a_2842_, v_upperBound_2834_);
if (v___x_2874_ == 0)
{
lean_object* v___x_2875_; 
lean_dec(v_a_2842_);
lean_dec_ref(v_postApp_2841_);
lean_dec_ref(v_post_2837_);
lean_dec_ref(v_pre_2836_);
v___x_2875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2875_, 0, v_b_2843_);
return v___x_2875_;
}
else
{
lean_object* v___x_2876_; lean_object* v___x_2877_; uint8_t v___x_2878_; 
v___x_2876_ = lean_array_fget_borrowed(v_b_2843_, v_a_2842_);
v___x_2877_ = lean_array_get_size(v___x_2835_);
v___x_2878_ = lean_nat_dec_lt(v_a_2842_, v___x_2877_);
if (v___x_2878_ == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___f_2882_; 
lean_inc(v___x_2876_);
v___x_2879_ = lean_box(v_usedLetOnly_2838_);
v___x_2880_ = lean_box(v_skipConstInApp_2839_);
v___x_2881_ = lean_box(v_skipInstances_2840_);
lean_inc(v_a_2842_);
lean_inc(v___y_2844_);
lean_inc_ref(v_postApp_2841_);
lean_inc_ref(v_post_2837_);
lean_inc_ref(v_pre_2836_);
v___f_2882_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_2882_, 0, v_pre_2836_);
lean_closure_set(v___f_2882_, 1, v_post_2837_);
lean_closure_set(v___f_2882_, 2, v___x_2879_);
lean_closure_set(v___f_2882_, 3, v___x_2880_);
lean_closure_set(v___f_2882_, 4, v___x_2881_);
lean_closure_set(v___f_2882_, 5, v_postApp_2841_);
lean_closure_set(v___f_2882_, 6, v___x_2876_);
lean_closure_set(v___f_2882_, 7, v___y_2844_);
lean_closure_set(v___f_2882_, 8, v_b_2843_);
lean_closure_set(v___f_2882_, 9, v_a_2842_);
v___y_2851_ = v___f_2882_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_2883_; uint8_t v_isInstance_2884_; 
v___x_2883_ = lean_array_fget_borrowed(v___x_2835_, v_a_2842_);
v_isInstance_2884_ = lean_ctor_get_uint8(v___x_2883_, sizeof(void*)*1 + 4);
if (v_isInstance_2884_ == 0)
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___f_2888_; 
lean_inc(v___x_2876_);
v___x_2885_ = lean_box(v_usedLetOnly_2838_);
v___x_2886_ = lean_box(v_skipConstInApp_2839_);
v___x_2887_ = lean_box(v_skipInstances_2840_);
lean_inc(v_a_2842_);
lean_inc(v___y_2844_);
lean_inc_ref(v_postApp_2841_);
lean_inc_ref(v_post_2837_);
lean_inc_ref(v_pre_2836_);
v___f_2888_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__0___boxed), 15, 10);
lean_closure_set(v___f_2888_, 0, v_pre_2836_);
lean_closure_set(v___f_2888_, 1, v_post_2837_);
lean_closure_set(v___f_2888_, 2, v___x_2885_);
lean_closure_set(v___f_2888_, 3, v___x_2886_);
lean_closure_set(v___f_2888_, 4, v___x_2887_);
lean_closure_set(v___f_2888_, 5, v_postApp_2841_);
lean_closure_set(v___f_2888_, 6, v___x_2876_);
lean_closure_set(v___f_2888_, 7, v___y_2844_);
lean_closure_set(v___f_2888_, 8, v_b_2843_);
lean_closure_set(v___f_2888_, 9, v_a_2842_);
v___y_2851_ = v___f_2888_;
goto v___jp_2850_;
}
else
{
lean_object* v___x_2889_; lean_object* v___f_2890_; 
v___x_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_b_2843_);
v___f_2890_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2890_, 0, v___x_2889_);
v___y_2851_ = v___f_2890_;
goto v___jp_2850_;
}
}
}
v___jp_2850_:
{
lean_object* v___x_2852_; 
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
v___x_2852_ = lean_apply_5(v___y_2851_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, lean_box(0));
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2865_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2865_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2865_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_a_2853_) == 0)
{
lean_object* v_a_2857_; lean_object* v___x_2859_; 
lean_dec(v_a_2842_);
lean_dec_ref(v_postApp_2841_);
lean_dec_ref(v_post_2837_);
lean_dec_ref(v_pre_2836_);
v_a_2857_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v_a_2853_, 1);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v_a_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_del_object(v___x_2855_);
v_a_2861_ = lean_ctor_get(v_a_2853_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v_a_2853_, 1);
v___x_2862_ = lean_unsigned_to_nat(1u);
v___x_2863_ = lean_nat_add(v_a_2842_, v___x_2862_);
lean_dec(v_a_2842_);
v_a_2842_ = v___x_2863_;
v_b_2843_ = v_a_2861_;
goto _start;
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2842_);
lean_dec_ref(v_postApp_2841_);
lean_dec_ref(v_post_2837_);
lean_dec_ref(v_pre_2836_);
v_a_2866_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2852_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2852_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2891_, lean_object* v_pre_2892_, lean_object* v_post_2893_, uint8_t v_usedLetOnly_2894_, uint8_t v_skipConstInApp_2895_, lean_object* v_postApp_2896_, lean_object* v___y_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_, lean_object* v_x_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v_f_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; 
if (lean_obj_tag(v_x_2898_) == 5)
{
lean_object* v_fn_2960_; lean_object* v_arg_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_fn_2960_ = lean_ctor_get(v_x_2898_, 0);
lean_inc_ref(v_fn_2960_);
v_arg_2961_ = lean_ctor_get(v_x_2898_, 1);
lean_inc_ref(v_arg_2961_);
lean_dec_ref_known(v_x_2898_, 2);
v___x_2962_ = lean_array_set(v_x_2899_, v_x_2900_, v_arg_2961_);
v___x_2963_ = lean_unsigned_to_nat(1u);
v___x_2964_ = lean_nat_sub(v_x_2900_, v___x_2963_);
lean_dec(v_x_2900_);
v_x_2898_ = v_fn_2960_;
v_x_2899_ = v___x_2962_;
v_x_2900_ = v___x_2964_;
goto _start;
}
else
{
lean_dec(v_x_2900_);
if (v_skipConstInApp_2895_ == 0)
{
goto v___jp_2957_;
}
else
{
uint8_t v___x_2966_; 
v___x_2966_ = l_Lean_Expr_isConst(v_x_2898_);
if (v___x_2966_ == 0)
{
goto v___jp_2957_;
}
else
{
v_f_2908_ = v_x_2898_;
v___y_2909_ = v___y_2901_;
v___y_2910_ = v___y_2902_;
v___y_2911_ = v___y_2903_;
v___y_2912_ = v___y_2904_;
v___y_2913_ = v___y_2905_;
goto v___jp_2907_;
}
}
}
v___jp_2907_:
{
if (v_skipInstances_2891_ == 0)
{
size_t v_sz_2914_; size_t v___x_2915_; lean_object* v___x_2916_; 
v_sz_2914_ = lean_array_size(v_x_2899_);
v___x_2915_ = ((size_t)0ULL);
lean_inc_ref(v_postApp_2896_);
lean_inc_ref(v_post_2893_);
lean_inc_ref(v_pre_2892_);
v___x_2916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2892_, v_post_2893_, v_usedLetOnly_2894_, v_skipConstInApp_2895_, v_skipInstances_2891_, v_postApp_2896_, v_sz_2914_, v___x_2915_, v_x_2899_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2916_) == 0)
{
lean_object* v_a_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_a_2917_);
lean_dec_ref_known(v___x_2916_, 1);
v___x_2918_ = l_Lean_mkAppN(v_f_2908_, v_a_2917_);
lean_dec(v_a_2917_);
lean_inc_ref(v_postApp_2896_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
lean_inc(v___y_2911_);
lean_inc_ref(v___y_2910_);
v___x_2919_ = lean_apply_7(v_postApp_2896_, v___y_2897_, v___x_2918_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, lean_box(0));
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2921_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
v___x_2921_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2892_, v_post_2893_, v_usedLetOnly_2894_, v_skipConstInApp_2895_, v_skipInstances_2891_, v_postApp_2896_, v_a_2920_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2921_;
}
else
{
lean_dec_ref(v_postApp_2896_);
lean_dec_ref(v_post_2893_);
lean_dec_ref(v_pre_2892_);
return v___x_2919_;
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v_f_2908_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_postApp_2896_);
lean_dec_ref(v_post_2893_);
lean_dec_ref(v_pre_2892_);
v_a_2922_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2916_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2916_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_array_get_size(v_x_2899_);
lean_inc_ref(v_f_2908_);
v___x_2931_ = l_Lean_Meta_getFunInfoNArgs(v_f_2908_, v___x_2930_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v_paramInfo_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2931_, 1);
v_paramInfo_2933_ = lean_ctor_get(v_a_2932_, 0);
lean_inc_ref(v_paramInfo_2933_);
lean_dec(v_a_2932_);
v___x_2934_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_postApp_2896_);
lean_inc_ref(v_post_2893_);
lean_inc_ref(v_pre_2892_);
v___x_2935_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v___x_2930_, v_paramInfo_2933_, v_pre_2892_, v_post_2893_, v_usedLetOnly_2894_, v_skipConstInApp_2895_, v_skipInstances_2891_, v_postApp_2896_, v___x_2934_, v_x_2899_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec_ref(v_paramInfo_2933_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = l_Lean_mkAppN(v_f_2908_, v_a_2936_);
lean_dec(v_a_2936_);
lean_inc_ref(v_postApp_2896_);
lean_inc(v___y_2913_);
lean_inc_ref(v___y_2912_);
lean_inc(v___y_2911_);
lean_inc_ref(v___y_2910_);
v___x_2938_ = lean_apply_7(v_postApp_2896_, v___y_2897_, v___x_2937_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, lean_box(0));
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2892_, v_post_2893_, v_usedLetOnly_2894_, v_skipConstInApp_2895_, v_skipInstances_2891_, v_postApp_2896_, v_a_2939_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2940_;
}
else
{
lean_dec_ref(v_postApp_2896_);
lean_dec_ref(v_post_2893_);
lean_dec_ref(v_pre_2892_);
return v___x_2938_;
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v_f_2908_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_postApp_2896_);
lean_dec_ref(v_post_2893_);
lean_dec_ref(v_pre_2892_);
v_a_2941_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2935_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2935_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_f_2908_);
lean_dec_ref(v_x_2899_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_postApp_2896_);
lean_dec_ref(v_post_2893_);
lean_dec_ref(v_pre_2892_);
v_a_2949_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2931_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2931_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
}
v___jp_2957_:
{
lean_object* v___x_2958_; 
lean_inc_ref(v_postApp_2896_);
lean_inc_ref(v_post_2893_);
lean_inc_ref(v_pre_2892_);
v___x_2958_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2892_, v_post_2893_, v_usedLetOnly_2894_, v_skipConstInApp_2895_, v_skipInstances_2891_, v_postApp_2896_, v_x_2898_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v_f_2908_ = v_a_2959_;
v___y_2909_ = v___y_2901_;
v___y_2910_ = v___y_2902_;
v___y_2911_ = v___y_2903_;
v___y_2912_ = v___y_2904_;
v___y_2913_ = v___y_2905_;
goto v___jp_2907_;
}
else
{
lean_dec_ref(v_x_2899_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_postApp_2896_);
lean_dec_ref(v_post_2893_);
lean_dec_ref(v_pre_2892_);
return v___x_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v___x_2967_, lean_object* v_pre_2968_, lean_object* v_e_2969_, lean_object* v_post_2970_, uint8_t v_usedLetOnly_2971_, uint8_t v_skipConstInApp_2972_, uint8_t v_skipInstances_2973_, lean_object* v_postApp_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Core_checkSystem(v___x_2967_, v___y_2978_, v___y_2979_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v___x_2982_; 
lean_dec_ref_known(v___x_2981_, 1);
lean_inc_ref(v_pre_2968_);
lean_inc(v___y_2979_);
lean_inc_ref(v___y_2978_);
lean_inc(v___y_2977_);
lean_inc_ref(v___y_2976_);
lean_inc_ref(v_e_2969_);
v___x_2982_ = lean_apply_6(v_pre_2968_, v_e_2969_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, lean_box(0));
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3031_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_3031_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3031_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___y_2988_; 
switch(lean_obj_tag(v_a_2983_))
{
case 0:
{
lean_object* v_e_3023_; lean_object* v___x_3025_; 
lean_dec_ref(v_postApp_2974_);
lean_dec_ref(v_post_2970_);
lean_dec_ref(v_e_2969_);
lean_dec_ref(v_pre_2968_);
v_e_3023_ = lean_ctor_get(v_a_2983_, 0);
lean_inc_ref(v_e_3023_);
lean_dec_ref_known(v_a_2983_, 1);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v_e_3023_);
v___x_3025_ = v___x_2985_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_e_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
case 1:
{
lean_object* v_e_3027_; lean_object* v___x_3028_; 
lean_del_object(v___x_2985_);
lean_dec_ref(v_e_2969_);
v_e_3027_ = lean_ctor_get(v_a_2983_, 0);
lean_inc_ref(v_e_3027_);
lean_dec_ref_known(v_a_2983_, 1);
v___x_3028_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v_e_3027_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_3028_;
}
default: 
{
lean_object* v_e_x3f_3029_; 
lean_del_object(v___x_2985_);
v_e_x3f_3029_ = lean_ctor_get(v_a_2983_, 0);
lean_inc(v_e_x3f_3029_);
lean_dec_ref_known(v_a_2983_, 1);
if (lean_obj_tag(v_e_x3f_3029_) == 0)
{
v___y_2988_ = v_e_2969_;
goto v___jp_2987_;
}
else
{
lean_object* v_val_3030_; 
lean_dec_ref(v_e_2969_);
v_val_3030_ = lean_ctor_get(v_e_x3f_3029_, 0);
lean_inc(v_val_3030_);
lean_dec_ref_known(v_e_x3f_3029_, 1);
v___y_2988_ = v_val_3030_;
goto v___jp_2987_;
}
}
}
v___jp_2987_:
{
switch(lean_obj_tag(v___y_2988_))
{
case 7:
{
lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2989_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2990_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___x_2989_, v___y_2988_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_2990_;
}
case 6:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___x_2991_, v___y_2988_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_2992_;
}
case 8:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2994_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___x_2993_, v___y_2988_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_2994_;
}
case 5:
{
lean_object* v_dummy_2995_; lean_object* v_nargs_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_dummy_2995_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_2996_ = l_Lean_Expr_getAppNumArgs(v___y_2988_);
lean_inc(v_nargs_2996_);
v___x_2997_ = lean_mk_array(v_nargs_2996_, v_dummy_2995_);
v___x_2998_ = lean_unsigned_to_nat(1u);
v___x_2999_ = lean_nat_sub(v_nargs_2996_, v___x_2998_);
lean_dec(v_nargs_2996_);
lean_inc_ref(v___y_2988_);
v___x_3000_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_2973_, v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_postApp_2974_, v___y_2988_, v___y_2988_, v___x_2997_, v___x_2999_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_3000_;
}
case 10:
{
lean_object* v_data_3001_; lean_object* v_expr_3002_; lean_object* v___x_3003_; 
v_data_3001_ = lean_ctor_get(v___y_2988_, 0);
v_expr_3002_ = lean_ctor_get(v___y_2988_, 1);
lean_inc_ref(v_expr_3002_);
lean_inc_ref(v_postApp_2974_);
lean_inc_ref(v_post_2970_);
lean_inc_ref(v_pre_2968_);
v___x_3003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v_expr_3002_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; size_t v___x_3005_; size_t v___x_3006_; uint8_t v___x_3007_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = lean_ptr_addr(v_expr_3002_);
v___x_3006_ = lean_ptr_addr(v_a_3004_);
v___x_3007_ = lean_usize_dec_eq(v___x_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_inc(v_data_3001_);
lean_dec_ref_known(v___y_2988_, 2);
v___x_3008_ = l_Lean_Expr_mdata___override(v_data_3001_, v_a_3004_);
v___x_3009_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___x_3008_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; 
lean_dec(v_a_3004_);
v___x_3010_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___y_2988_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_3010_;
}
}
else
{
lean_dec_ref_known(v___y_2988_, 2);
lean_dec_ref(v_postApp_2974_);
lean_dec_ref(v_post_2970_);
lean_dec_ref(v_pre_2968_);
return v___x_3003_;
}
}
case 11:
{
lean_object* v_typeName_3011_; lean_object* v_idx_3012_; lean_object* v_struct_3013_; lean_object* v___x_3014_; 
v_typeName_3011_ = lean_ctor_get(v___y_2988_, 0);
v_idx_3012_ = lean_ctor_get(v___y_2988_, 1);
v_struct_3013_ = lean_ctor_get(v___y_2988_, 2);
lean_inc_ref(v_struct_3013_);
lean_inc_ref(v_postApp_2974_);
lean_inc_ref(v_post_2970_);
lean_inc_ref(v_pre_2968_);
v___x_3014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v_struct_3013_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; size_t v___x_3016_; size_t v___x_3017_; uint8_t v___x_3018_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_ptr_addr(v_struct_3013_);
v___x_3017_ = lean_ptr_addr(v_a_3015_);
v___x_3018_ = lean_usize_dec_eq(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_inc(v_idx_3012_);
lean_inc(v_typeName_3011_);
lean_dec_ref_known(v___y_2988_, 3);
v___x_3019_ = l_Lean_Expr_proj___override(v_typeName_3011_, v_idx_3012_, v_a_3015_);
v___x_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___x_3019_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
lean_dec(v_a_3015_);
v___x_3021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___y_2988_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_3021_;
}
}
else
{
lean_dec_ref_known(v___y_2988_, 3);
lean_dec_ref(v_postApp_2974_);
lean_dec_ref(v_post_2970_);
lean_dec_ref(v_pre_2968_);
return v___x_3014_;
}
}
default: 
{
lean_object* v___x_3022_; 
v___x_3022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_2968_, v_post_2970_, v_usedLetOnly_2971_, v_skipConstInApp_2972_, v_skipInstances_2973_, v_postApp_2974_, v___y_2988_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
return v___x_3022_;
}
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_postApp_2974_);
lean_dec_ref(v_post_2970_);
lean_dec_ref(v_e_2969_);
lean_dec_ref(v_pre_2968_);
v_a_3032_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2982_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2982_);
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
lean_dec_ref(v_postApp_2974_);
lean_dec_ref(v_post_2970_);
lean_dec_ref(v_e_2969_);
lean_dec_ref(v_pre_2968_);
v_a_3040_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2981_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2981_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v___x_3048_, lean_object* v_pre_3049_, lean_object* v_e_3050_, lean_object* v_post_3051_, lean_object* v_usedLetOnly_3052_, lean_object* v_skipConstInApp_3053_, lean_object* v_skipInstances_3054_, lean_object* v_postApp_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_){
_start:
{
uint8_t v_usedLetOnly_boxed_3062_; uint8_t v_skipConstInApp_boxed_3063_; uint8_t v_skipInstances_boxed_3064_; lean_object* v_res_3065_; 
v_usedLetOnly_boxed_3062_ = lean_unbox(v_usedLetOnly_3052_);
v_skipConstInApp_boxed_3063_ = lean_unbox(v_skipConstInApp_3053_);
v_skipInstances_boxed_3064_ = lean_unbox(v_skipInstances_3054_);
v_res_3065_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v___x_3048_, v_pre_3049_, v_e_3050_, v_post_3051_, v_usedLetOnly_boxed_3062_, v_skipConstInApp_boxed_3063_, v_skipInstances_boxed_3064_, v_postApp_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3066_, lean_object* v_post_3067_, uint8_t v_usedLetOnly_3068_, uint8_t v_skipConstInApp_3069_, uint8_t v_skipInstances_3070_, lean_object* v_postApp_3071_, lean_object* v_e_3072_, lean_object* v_a_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
lean_inc(v_a_3073_);
v___x_3079_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3079_, 0, lean_box(0));
lean_closure_set(v___x_3079_, 1, lean_box(0));
lean_closure_set(v___x_3079_, 2, v_a_3073_);
v___x_3080_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3079_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3115_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3083_ = v___x_3080_;
v_isShared_3084_ = v_isSharedCheck_3115_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3115_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3085_; 
v___x_3085_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg(v_a_3081_, v_e_3072_);
lean_dec(v_a_3081_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; 
lean_del_object(v___x_3083_);
v___x_3086_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
v___x_3087_ = lean_box(v_usedLetOnly_3068_);
v___x_3088_ = lean_box(v_skipConstInApp_3069_);
v___x_3089_ = lean_box(v_skipInstances_3070_);
lean_inc_ref(v_e_3072_);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 14, 8);
lean_closure_set(v___f_3090_, 0, v___x_3086_);
lean_closure_set(v___f_3090_, 1, v_pre_3066_);
lean_closure_set(v___f_3090_, 2, v_e_3072_);
lean_closure_set(v___f_3090_, 3, v_post_3067_);
lean_closure_set(v___f_3090_, 4, v___x_3087_);
lean_closure_set(v___f_3090_, 5, v___x_3088_);
lean_closure_set(v___f_3090_, 6, v___x_3089_);
lean_closure_set(v___f_3090_, 7, v_postApp_3071_);
v___x_3091_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3090_, v_a_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_object* v_a_3092_; lean_object* v___f_3093_; lean_object* v___x_3094_; 
v_a_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc_n(v_a_3092_, 2);
lean_dec_ref_known(v___x_3091_, 1);
lean_inc(v_a_3073_);
v___f_3093_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3093_, 0, v_a_3073_);
lean_closure_set(v___f_3093_, 1, v_e_3072_);
lean_closure_set(v___f_3093_, 2, v_a_3092_);
v___x_3094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3093_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v___x_3094_, 0);
lean_dec(v_unused_3102_);
v___x_3096_ = v___x_3094_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_dec(v___x_3094_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v_a_3092_);
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3092_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec(v_a_3092_);
v_a_3103_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3094_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3094_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_dec_ref(v_e_3072_);
return v___x_3091_;
}
}
else
{
lean_object* v_val_3111_; lean_object* v___x_3113_; 
lean_dec_ref(v_e_3072_);
lean_dec_ref(v_postApp_3071_);
lean_dec_ref(v_post_3067_);
lean_dec_ref(v_pre_3066_);
v_val_3111_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_val_3111_);
lean_dec_ref_known(v___x_3085_, 1);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v_val_3111_);
v___x_3113_ = v___x_3083_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_val_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref(v_e_3072_);
lean_dec_ref(v_postApp_3071_);
lean_dec_ref(v_post_3067_);
lean_dec_ref(v_pre_3066_);
v_a_3116_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3080_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3080_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3124_, lean_object* v_post_3125_, uint8_t v_usedLetOnly_3126_, uint8_t v_skipConstInApp_3127_, uint8_t v_skipInstances_3128_, lean_object* v_postApp_3129_, lean_object* v_fvars_3130_, lean_object* v_e_3131_, lean_object* v_a_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
if (lean_obj_tag(v_e_3131_) == 7)
{
lean_object* v_binderName_3138_; lean_object* v_binderType_3139_; lean_object* v_body_3140_; uint8_t v_binderInfo_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
v_binderName_3138_ = lean_ctor_get(v_e_3131_, 0);
lean_inc(v_binderName_3138_);
v_binderType_3139_ = lean_ctor_get(v_e_3131_, 1);
lean_inc_ref(v_binderType_3139_);
v_body_3140_ = lean_ctor_get(v_e_3131_, 2);
lean_inc_ref(v_body_3140_);
v_binderInfo_3141_ = lean_ctor_get_uint8(v_e_3131_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3131_, 3);
v___x_3142_ = lean_box(v_usedLetOnly_3126_);
v___x_3143_ = lean_box(v_skipConstInApp_3127_);
v___x_3144_ = lean_box(v_skipInstances_3128_);
lean_inc_ref(v_postApp_3129_);
lean_inc_ref(v_post_3125_);
lean_inc_ref(v_pre_3124_);
lean_inc_ref(v_fvars_3130_);
v___f_3145_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 15, 8);
lean_closure_set(v___f_3145_, 0, v_fvars_3130_);
lean_closure_set(v___f_3145_, 1, v_pre_3124_);
lean_closure_set(v___f_3145_, 2, v_post_3125_);
lean_closure_set(v___f_3145_, 3, v___x_3142_);
lean_closure_set(v___f_3145_, 4, v___x_3143_);
lean_closure_set(v___f_3145_, 5, v___x_3144_);
lean_closure_set(v___f_3145_, 6, v_postApp_3129_);
lean_closure_set(v___f_3145_, 7, v_body_3140_);
v___x_3146_ = lean_expr_instantiate_rev(v_binderType_3139_, v_fvars_3130_);
lean_dec_ref(v_fvars_3130_);
lean_dec_ref(v_binderType_3139_);
v___x_3147_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3128_, v_postApp_3129_, v___x_3146_, v_a_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_object* v_a_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; 
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref_known(v___x_3147_, 1);
v___x_3149_ = 0;
v___x_3150_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3138_, v_binderInfo_3141_, v_a_3148_, v___f_3145_, v___x_3149_, v_a_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3150_;
}
else
{
lean_dec_ref(v___f_3145_);
lean_dec(v_binderName_3138_);
return v___x_3147_;
}
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = lean_expr_instantiate_rev(v_e_3131_, v_fvars_3130_);
lean_dec_ref(v_e_3131_);
lean_inc_ref(v_postApp_3129_);
lean_inc_ref(v_post_3125_);
lean_inc_ref(v_pre_3124_);
v___x_3152_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3128_, v_postApp_3129_, v___x_3151_, v_a_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; uint8_t v___x_3154_; uint8_t v___x_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = 0;
v___x_3155_ = 1;
v___x_3156_ = 1;
v___x_3157_ = l_Lean_Meta_mkForallFVars(v_fvars_3130_, v_a_3153_, v___x_3154_, v_usedLetOnly_3126_, v___x_3155_, v___x_3156_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec_ref(v_fvars_3130_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3159_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
v___x_3159_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_3124_, v_post_3125_, v_usedLetOnly_3126_, v_skipConstInApp_3127_, v_skipInstances_3128_, v_postApp_3129_, v_a_3158_, v_a_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
return v___x_3159_;
}
else
{
lean_dec_ref(v_postApp_3129_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
return v___x_3157_;
}
}
else
{
lean_dec_ref(v_fvars_3130_);
lean_dec_ref(v_postApp_3129_);
lean_dec_ref(v_post_3125_);
lean_dec_ref(v_pre_3124_);
return v___x_3152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3160_, lean_object* v_pre_3161_, lean_object* v_post_3162_, uint8_t v_usedLetOnly_3163_, uint8_t v_skipConstInApp_3164_, uint8_t v_skipInstances_3165_, lean_object* v_postApp_3166_, lean_object* v_body_3167_, lean_object* v_x_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_array_push(v_fvars_3160_, v_x_3168_);
v___x_3176_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3161_, v_post_3162_, v_usedLetOnly_3163_, v_skipConstInApp_3164_, v_skipInstances_3165_, v_postApp_3166_, v___x_3175_, v_body_3167_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object* v_pre_3177_, lean_object* v_post_3178_, lean_object* v_usedLetOnly_3179_, lean_object* v_skipConstInApp_3180_, lean_object* v_skipInstances_3181_, lean_object* v_postApp_3182_, lean_object* v_e_3183_, lean_object* v_a_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v_usedLetOnly_boxed_3190_; uint8_t v_skipConstInApp_boxed_3191_; uint8_t v_skipInstances_boxed_3192_; lean_object* v_res_3193_; 
v_usedLetOnly_boxed_3190_ = lean_unbox(v_usedLetOnly_3179_);
v_skipConstInApp_boxed_3191_ = lean_unbox(v_skipConstInApp_3180_);
v_skipInstances_boxed_3192_ = lean_unbox(v_skipInstances_3181_);
v_res_3193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_pre_3177_, v_post_3178_, v_usedLetOnly_boxed_3190_, v_skipConstInApp_boxed_3191_, v_skipInstances_boxed_3192_, v_postApp_3182_, v_e_3183_, v_a_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v_a_3184_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3194_, lean_object* v_post_3195_, lean_object* v_usedLetOnly_3196_, lean_object* v_skipConstInApp_3197_, lean_object* v_skipInstances_3198_, lean_object* v_postApp_3199_, lean_object* v_sz_3200_, lean_object* v_i_3201_, lean_object* v_bs_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v_usedLetOnly_boxed_3209_; uint8_t v_skipConstInApp_boxed_3210_; uint8_t v_skipInstances_boxed_3211_; size_t v_sz_boxed_3212_; size_t v_i_boxed_3213_; lean_object* v_res_3214_; 
v_usedLetOnly_boxed_3209_ = lean_unbox(v_usedLetOnly_3196_);
v_skipConstInApp_boxed_3210_ = lean_unbox(v_skipConstInApp_3197_);
v_skipInstances_boxed_3211_ = lean_unbox(v_skipInstances_3198_);
v_sz_boxed_3212_ = lean_unbox_usize(v_sz_3200_);
lean_dec(v_sz_3200_);
v_i_boxed_3213_ = lean_unbox_usize(v_i_3201_);
lean_dec(v_i_3201_);
v_res_3214_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3194_, v_post_3195_, v_usedLetOnly_boxed_3209_, v_skipConstInApp_boxed_3210_, v_skipInstances_boxed_3211_, v_postApp_3199_, v_sz_boxed_3212_, v_i_boxed_3213_, v_bs_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3215_, lean_object* v_post_3216_, lean_object* v_usedLetOnly_3217_, lean_object* v_skipConstInApp_3218_, lean_object* v_skipInstances_3219_, lean_object* v_postApp_3220_, lean_object* v_e_3221_, lean_object* v_a_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_){
_start:
{
uint8_t v_usedLetOnly_boxed_3228_; uint8_t v_skipConstInApp_boxed_3229_; uint8_t v_skipInstances_boxed_3230_; lean_object* v_res_3231_; 
v_usedLetOnly_boxed_3228_ = lean_unbox(v_usedLetOnly_3217_);
v_skipConstInApp_boxed_3229_ = lean_unbox(v_skipConstInApp_3218_);
v_skipInstances_boxed_3230_ = lean_unbox(v_skipInstances_3219_);
v_res_3231_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3215_, v_post_3216_, v_usedLetOnly_boxed_3228_, v_skipConstInApp_boxed_3229_, v_skipInstances_boxed_3230_, v_postApp_3220_, v_e_3221_, v_a_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v_a_3222_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3232_, lean_object* v_post_3233_, lean_object* v_usedLetOnly_3234_, lean_object* v_skipConstInApp_3235_, lean_object* v_skipInstances_3236_, lean_object* v_postApp_3237_, lean_object* v_fvars_3238_, lean_object* v_e_3239_, lean_object* v_a_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
uint8_t v_usedLetOnly_boxed_3246_; uint8_t v_skipConstInApp_boxed_3247_; uint8_t v_skipInstances_boxed_3248_; lean_object* v_res_3249_; 
v_usedLetOnly_boxed_3246_ = lean_unbox(v_usedLetOnly_3234_);
v_skipConstInApp_boxed_3247_ = lean_unbox(v_skipConstInApp_3235_);
v_skipInstances_boxed_3248_ = lean_unbox(v_skipInstances_3236_);
v_res_3249_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3232_, v_post_3233_, v_usedLetOnly_boxed_3246_, v_skipConstInApp_boxed_3247_, v_skipInstances_boxed_3248_, v_postApp_3237_, v_fvars_3238_, v_e_3239_, v_a_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v_a_3240_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3250_, lean_object* v_post_3251_, lean_object* v_usedLetOnly_3252_, lean_object* v_skipConstInApp_3253_, lean_object* v_skipInstances_3254_, lean_object* v_postApp_3255_, lean_object* v_fvars_3256_, lean_object* v_e_3257_, lean_object* v_a_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
uint8_t v_usedLetOnly_boxed_3264_; uint8_t v_skipConstInApp_boxed_3265_; uint8_t v_skipInstances_boxed_3266_; lean_object* v_res_3267_; 
v_usedLetOnly_boxed_3264_ = lean_unbox(v_usedLetOnly_3252_);
v_skipConstInApp_boxed_3265_ = lean_unbox(v_skipConstInApp_3253_);
v_skipInstances_boxed_3266_ = lean_unbox(v_skipInstances_3254_);
v_res_3267_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3250_, v_post_3251_, v_usedLetOnly_boxed_3264_, v_skipConstInApp_boxed_3265_, v_skipInstances_boxed_3266_, v_postApp_3255_, v_fvars_3256_, v_e_3257_, v_a_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
lean_dec(v_a_3258_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3268_, lean_object* v_post_3269_, lean_object* v_usedLetOnly_3270_, lean_object* v_skipConstInApp_3271_, lean_object* v_skipInstances_3272_, lean_object* v_postApp_3273_, lean_object* v_fvars_3274_, lean_object* v_e_3275_, lean_object* v_a_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_){
_start:
{
uint8_t v_usedLetOnly_boxed_3282_; uint8_t v_skipConstInApp_boxed_3283_; uint8_t v_skipInstances_boxed_3284_; lean_object* v_res_3285_; 
v_usedLetOnly_boxed_3282_ = lean_unbox(v_usedLetOnly_3270_);
v_skipConstInApp_boxed_3283_ = lean_unbox(v_skipConstInApp_3271_);
v_skipInstances_boxed_3284_ = lean_unbox(v_skipInstances_3272_);
v_res_3285_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3268_, v_post_3269_, v_usedLetOnly_boxed_3282_, v_skipConstInApp_boxed_3283_, v_skipInstances_boxed_3284_, v_postApp_3273_, v_fvars_3274_, v_e_3275_, v_a_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v___y_3278_);
lean_dec_ref(v___y_3277_);
lean_dec(v_a_3276_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_upperBound_3286_, lean_object* v___x_3287_, lean_object* v_pre_3288_, lean_object* v_post_3289_, lean_object* v_usedLetOnly_3290_, lean_object* v_skipConstInApp_3291_, lean_object* v_skipInstances_3292_, lean_object* v_postApp_3293_, lean_object* v_a_3294_, lean_object* v_b_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
uint8_t v_usedLetOnly_boxed_3302_; uint8_t v_skipConstInApp_boxed_3303_; uint8_t v_skipInstances_boxed_3304_; lean_object* v_res_3305_; 
v_usedLetOnly_boxed_3302_ = lean_unbox(v_usedLetOnly_3290_);
v_skipConstInApp_boxed_3303_ = lean_unbox(v_skipConstInApp_3291_);
v_skipInstances_boxed_3304_ = lean_unbox(v_skipInstances_3292_);
v_res_3305_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_upperBound_3286_, v___x_3287_, v_pre_3288_, v_post_3289_, v_usedLetOnly_boxed_3302_, v_skipConstInApp_boxed_3303_, v_skipInstances_boxed_3304_, v_postApp_3293_, v_a_3294_, v_b_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec_ref(v___x_3287_);
lean_dec(v_upperBound_3286_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3306_, lean_object* v_pre_3307_, lean_object* v_post_3308_, lean_object* v_usedLetOnly_3309_, lean_object* v_skipConstInApp_3310_, lean_object* v_postApp_3311_, lean_object* v___y_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v_skipInstances_boxed_3322_; uint8_t v_usedLetOnly_boxed_3323_; uint8_t v_skipConstInApp_boxed_3324_; lean_object* v_res_3325_; 
v_skipInstances_boxed_3322_ = lean_unbox(v_skipInstances_3306_);
v_usedLetOnly_boxed_3323_ = lean_unbox(v_usedLetOnly_3309_);
v_skipConstInApp_boxed_3324_ = lean_unbox(v_skipConstInApp_3310_);
v_res_3325_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3322_, v_pre_3307_, v_post_3308_, v_usedLetOnly_boxed_3323_, v_skipConstInApp_boxed_3324_, v_postApp_3311_, v___y_3312_, v_x_3313_, v_x_3314_, v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__1(lean_object* v_x_3326_, lean_object* v_e_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; 
v___x_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3333_, 0, v_e_3327_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__1___boxed(lean_object* v_x_3334_, lean_object* v_e_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__1(v_x_3334_, v_e_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec_ref(v_x_3334_);
return v_res_3341_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_unsigned_to_nat(16u);
v___x_3345_ = lean_mk_array(v___x_3344_, v___x_3343_);
return v___x_3345_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3346_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3347_ = lean_unsigned_to_nat(0u);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___x_3346_);
return v___x_3348_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3350_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3350_, 0, lean_box(0));
lean_closure_set(v___x_3350_, 1, lean_box(0));
lean_closure_set(v___x_3350_, 2, v___x_3349_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3351_, lean_object* v_pre_3352_, lean_object* v_post_3353_, uint8_t v_usedLetOnly_3354_, uint8_t v_skipConstInApp_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___f_3361_; uint8_t v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v_a_3365_; lean_object* v___x_3366_; 
v___f_3361_ = ((lean_object*)(l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0));
v___x_3362_ = 0;
v___x_3363_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3);
v___x_3364_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3363_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3364_);
v___x_3366_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3352_, v_post_3353_, v_usedLetOnly_3354_, v_skipConstInApp_3355_, v___x_3362_, v___f_3361_, v_input_3351_, v_a_3365_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v___x_3368_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3368_, 0, lean_box(0));
lean_closure_set(v___x_3368_, 1, lean_box(0));
lean_closure_set(v___x_3368_, 2, v_a_3365_);
v___x_3369_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3368_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3376_ == 0)
{
lean_object* v_unused_3377_; 
v_unused_3377_ = lean_ctor_get(v___x_3369_, 0);
lean_dec(v_unused_3377_);
v___x_3371_ = v___x_3369_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3369_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v_a_3367_);
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3367_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
else
{
lean_dec(v_a_3365_);
return v___x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3378_, lean_object* v_pre_3379_, lean_object* v_post_3380_, lean_object* v_usedLetOnly_3381_, lean_object* v_skipConstInApp_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
uint8_t v_usedLetOnly_boxed_3388_; uint8_t v_skipConstInApp_boxed_3389_; lean_object* v_res_3390_; 
v_usedLetOnly_boxed_3388_ = lean_unbox(v_usedLetOnly_3381_);
v_skipConstInApp_boxed_3389_ = lean_unbox(v_skipConstInApp_3382_);
v_res_3390_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3378_, v_pre_3379_, v_post_3380_, v_usedLetOnly_boxed_3388_, v_skipConstInApp_boxed_3389_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_){
_start:
{
lean_object* v___f_3399_; lean_object* v___f_3400_; uint8_t v___x_3401_; lean_object* v___x_3402_; 
v___f_3399_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3400_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3401_ = 0;
v___x_3402_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3393_, v___f_3400_, v___f_3399_, v___x_3401_, v___x_3401_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_00_u03b2_3410_, lean_object* v_m_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg(v_m_3411_, v_a_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3414_, lean_object* v_m_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_00_u03b2_3414_, v_m_3415_, v_a_3416_);
lean_dec_ref(v_a_3416_);
lean_dec_ref(v_m_3415_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_upperBound_3418_, lean_object* v___x_3419_, lean_object* v_pre_3420_, lean_object* v_post_3421_, uint8_t v_usedLetOnly_3422_, uint8_t v_skipConstInApp_3423_, uint8_t v_skipInstances_3424_, lean_object* v_postApp_3425_, lean_object* v___x_3426_, lean_object* v_inst_3427_, lean_object* v_R_3428_, lean_object* v_a_3429_, lean_object* v_b_3430_, lean_object* v_c_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_upperBound_3418_, v___x_3419_, v_pre_3420_, v_post_3421_, v_usedLetOnly_3422_, v_skipConstInApp_3423_, v_skipInstances_3424_, v_postApp_3425_, v_a_3429_, v_b_3430_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object** _args){
lean_object* v_upperBound_3439_ = _args[0];
lean_object* v___x_3440_ = _args[1];
lean_object* v_pre_3441_ = _args[2];
lean_object* v_post_3442_ = _args[3];
lean_object* v_usedLetOnly_3443_ = _args[4];
lean_object* v_skipConstInApp_3444_ = _args[5];
lean_object* v_skipInstances_3445_ = _args[6];
lean_object* v_postApp_3446_ = _args[7];
lean_object* v___x_3447_ = _args[8];
lean_object* v_inst_3448_ = _args[9];
lean_object* v_R_3449_ = _args[10];
lean_object* v_a_3450_ = _args[11];
lean_object* v_b_3451_ = _args[12];
lean_object* v_c_3452_ = _args[13];
lean_object* v___y_3453_ = _args[14];
lean_object* v___y_3454_ = _args[15];
lean_object* v___y_3455_ = _args[16];
lean_object* v___y_3456_ = _args[17];
lean_object* v___y_3457_ = _args[18];
lean_object* v___y_3458_ = _args[19];
_start:
{
uint8_t v_usedLetOnly_boxed_3459_; uint8_t v_skipConstInApp_boxed_3460_; uint8_t v_skipInstances_boxed_3461_; lean_object* v_res_3462_; 
v_usedLetOnly_boxed_3459_ = lean_unbox(v_usedLetOnly_3443_);
v_skipConstInApp_boxed_3460_ = lean_unbox(v_skipConstInApp_3444_);
v_skipInstances_boxed_3461_ = lean_unbox(v_skipInstances_3445_);
v_res_3462_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_upperBound_3439_, v___x_3440_, v_pre_3441_, v_post_3442_, v_usedLetOnly_boxed_3459_, v_skipConstInApp_boxed_3460_, v_skipInstances_boxed_3461_, v_postApp_3446_, v___x_3447_, v_inst_3448_, v_R_3449_, v_a_3450_, v_b_3451_, v_c_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec(v___y_3453_);
lean_dec(v___x_3447_);
lean_dec_ref(v___x_3440_);
lean_dec(v_upperBound_3439_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3463_, lean_object* v_name_3464_, uint8_t v_bi_3465_, lean_object* v_type_3466_, lean_object* v_k_3467_, uint8_t v_kind_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3464_, v_bi_3465_, v_type_3466_, v_k_3467_, v_kind_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3476_, lean_object* v_name_3477_, lean_object* v_bi_3478_, lean_object* v_type_3479_, lean_object* v_k_3480_, lean_object* v_kind_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
uint8_t v_bi_boxed_3488_; uint8_t v_kind_boxed_3489_; lean_object* v_res_3490_; 
v_bi_boxed_3488_ = lean_unbox(v_bi_3478_);
v_kind_boxed_3489_ = lean_unbox(v_kind_3481_);
v_res_3490_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3476_, v_name_3477_, v_bi_boxed_3488_, v_type_3479_, v_k_3480_, v_kind_boxed_3489_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3491_, lean_object* v_name_3492_, lean_object* v_type_3493_, lean_object* v_val_3494_, lean_object* v_k_3495_, uint8_t v_nondep_3496_, uint8_t v_kind_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3492_, v_type_3493_, v_val_3494_, v_k_3495_, v_nondep_3496_, v_kind_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3505_, lean_object* v_name_3506_, lean_object* v_type_3507_, lean_object* v_val_3508_, lean_object* v_k_3509_, lean_object* v_nondep_3510_, lean_object* v_kind_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v_nondep_boxed_3518_; uint8_t v_kind_boxed_3519_; lean_object* v_res_3520_; 
v_nondep_boxed_3518_ = lean_unbox(v_nondep_3510_);
v_kind_boxed_3519_ = lean_unbox(v_kind_3511_);
v_res_3520_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3505_, v_name_3506_, v_type_3507_, v_val_3508_, v_k_3509_, v_nondep_boxed_3518_, v_kind_boxed_3519_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_, v___y_3516_);
lean_dec(v___y_3516_);
lean_dec_ref(v___y_3515_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3521_, lean_object* v_ref_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3522_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3529_, lean_object* v_ref_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3529_, v_ref_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3537_, lean_object* v_x_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3546_, lean_object* v_x_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3546_, v_x_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3555_, lean_object* v_m_3556_, lean_object* v_a_3557_, lean_object* v_b_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3556_, v_a_3557_, v_b_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_3560_, lean_object* v_a_3561_, lean_object* v_x_3562_){
_start:
{
lean_object* v___x_3563_; 
v___x_3563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___redArg(v_a_3561_, v_x_3562_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3564_, lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_spec__5(v_00_u03b2_3564_, v_a_3565_, v_x_3566_);
lean_dec(v_x_3566_);
lean_dec_ref(v_a_3565_);
return v_res_3567_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3568_, lean_object* v_a_3569_, lean_object* v_x_3570_){
_start:
{
uint8_t v___x_3571_; 
v___x_3571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3569_, v_x_3570_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3572_, lean_object* v_a_3573_, lean_object* v_x_3574_){
_start:
{
uint8_t v_res_3575_; lean_object* v_r_3576_; 
v_res_3575_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3572_, v_a_3573_, v_x_3574_);
lean_dec(v_x_3574_);
lean_dec_ref(v_a_3573_);
v_r_3576_ = lean_box(v_res_3575_);
return v_r_3576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3577_, lean_object* v_data_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3580_, lean_object* v_a_3581_, lean_object* v_b_3582_, lean_object* v_x_3583_){
_start:
{
lean_object* v___x_3584_; 
v___x_3584_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3581_, v_b_3582_, v_x_3583_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3585_, lean_object* v_i_3586_, lean_object* v_source_3587_, lean_object* v_target_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3586_, v_source_3587_, v_target_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3591_, v_x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3594_, lean_object* v_opt_3595_){
_start:
{
lean_object* v_name_3596_; lean_object* v_defValue_3597_; lean_object* v_map_3598_; lean_object* v___x_3599_; 
v_name_3596_ = lean_ctor_get(v_opt_3595_, 0);
v_defValue_3597_ = lean_ctor_get(v_opt_3595_, 1);
v_map_3598_ = lean_ctor_get(v_opts_3594_, 0);
v___x_3599_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3598_, v_name_3596_);
if (lean_obj_tag(v___x_3599_) == 0)
{
uint8_t v___x_3600_; 
v___x_3600_ = lean_unbox(v_defValue_3597_);
return v___x_3600_;
}
else
{
lean_object* v_val_3601_; 
v_val_3601_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_val_3601_);
lean_dec_ref_known(v___x_3599_, 1);
if (lean_obj_tag(v_val_3601_) == 1)
{
uint8_t v_v_3602_; 
v_v_3602_ = lean_ctor_get_uint8(v_val_3601_, 0);
lean_dec_ref_known(v_val_3601_, 0);
return v_v_3602_;
}
else
{
uint8_t v___x_3603_; 
lean_dec(v_val_3601_);
v___x_3603_ = lean_unbox(v_defValue_3597_);
return v___x_3603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3604_, lean_object* v_opt_3605_){
_start:
{
uint8_t v_res_3606_; lean_object* v_r_3607_; 
v_res_3606_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3604_, v_opt_3605_);
lean_dec_ref(v_opt_3605_);
lean_dec_ref(v_opts_3604_);
v_r_3607_ = lean_box(v_res_3606_);
return v_r_3607_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
return v___x_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg(){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___boxed(lean_object* v___dummy_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
return v_res_3613_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
return v___x_3614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(lean_object* v_e_3617_, lean_object* v_k_3618_, uint8_t v_cleanupAnnotations_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___f_3625_; uint8_t v___x_3626_; uint8_t v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___f_3625_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3625_, 0, v_k_3618_);
v___x_3626_ = 1;
v___x_3627_ = 0;
v___x_3628_ = lean_box(0);
v___x_3629_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3617_, v___x_3626_, v___x_3627_, v___x_3626_, v___x_3627_, v___x_3628_, v___f_3625_, v_cleanupAnnotations_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3629_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3629_);
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
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
v_a_3638_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3629_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3629_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg___boxed(lean_object* v_e_3646_, lean_object* v_k_3647_, lean_object* v_cleanupAnnotations_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3654_; lean_object* v_res_3655_; 
v_cleanupAnnotations_boxed_3654_ = lean_unbox(v_cleanupAnnotations_3648_);
v_res_3655_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3646_, v_k_3647_, v_cleanupAnnotations_boxed_3654_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_00_u03b1_3656_, lean_object* v_e_3657_, lean_object* v_k_3658_, uint8_t v_cleanupAnnotations_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3657_, v_k_3658_, v_cleanupAnnotations_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_00_u03b1_3666_, lean_object* v_e_3667_, lean_object* v_k_3668_, lean_object* v_cleanupAnnotations_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3675_; lean_object* v_res_3676_; 
v_cleanupAnnotations_boxed_3675_ = lean_unbox(v_cleanupAnnotations_3669_);
v_res_3676_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(v_00_u03b1_3666_, v_e_3667_, v_k_3668_, v_cleanupAnnotations_boxed_3675_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3677_, lean_object* v_x_3678_, lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3677_) == 5)
{
lean_object* v_fn_3684_; lean_object* v_arg_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v_fn_3684_ = lean_ctor_get(v_x_3677_, 0);
lean_inc_ref(v_fn_3684_);
v_arg_3685_ = lean_ctor_get(v_x_3677_, 1);
lean_inc_ref(v_arg_3685_);
lean_dec_ref_known(v_x_3677_, 2);
v___x_3686_ = lean_array_set(v_x_3678_, v_x_3679_, v_arg_3685_);
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = lean_nat_sub(v_x_3679_, v___x_3687_);
lean_dec(v_x_3679_);
v_x_3677_ = v_fn_3684_;
v_x_3678_ = v___x_3686_;
v_x_3679_ = v___x_3688_;
goto _start;
}
else
{
lean_object* v___x_3690_; uint8_t v___x_3691_; 
lean_dec(v_x_3679_);
v___x_3690_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3691_ = l_Lean_Expr_isConstOf(v_x_3677_, v___x_3690_);
lean_dec_ref(v_x_3677_);
if (v___x_3691_ == 0)
{
lean_dec_ref(v_x_3678_);
goto v___jp_3681_;
}
else
{
lean_object* v___x_3692_; lean_object* v___x_3693_; uint8_t v___x_3694_; 
v___x_3692_ = lean_unsigned_to_nat(2u);
v___x_3693_ = lean_array_get_size(v_x_3678_);
v___x_3694_ = lean_nat_dec_le(v___x_3692_, v___x_3693_);
if (v___x_3694_ == 0)
{
lean_dec_ref(v_x_3678_);
goto v___jp_3681_;
}
else
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3695_ = lean_unsigned_to_nat(1u);
v___x_3696_ = lean_array_fget(v_x_3678_, v___x_3695_);
v___x_3697_ = l_Array_toSubarray___redArg(v_x_3678_, v___x_3692_, v___x_3693_);
v___x_3698_ = l_Subarray_copy___redArg(v___x_3697_);
v___x_3699_ = l_Lean_mkAppN(v___x_3696_, v___x_3698_);
lean_dec_ref(v___x_3698_);
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
return v___x_3702_;
}
}
}
v___jp_3681_:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3703_, lean_object* v_x_3704_, lean_object* v_x_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_res_3707_; 
v_res_3707_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3703_, v_x_3704_, v_x_3705_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(lean_object* v_e_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_dummy_3714_; lean_object* v_nargs_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v_dummy_3714_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3715_ = l_Lean_Expr_getAppNumArgs(v_e_3708_);
lean_inc(v_nargs_3715_);
v___x_3716_ = lean_mk_array(v_nargs_3715_, v_dummy_3714_);
v___x_3717_ = lean_unsigned_to_nat(1u);
v___x_3718_ = lean_nat_sub(v_nargs_3715_, v___x_3717_);
lean_dec(v_nargs_3715_);
v___x_3719_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3708_, v___x_3716_, v___x_3718_);
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v_e_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Elab_WF_preprocess___lam__0(v_e_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(lean_object* v_ref_3727_){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_ref_3727_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_ref_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3732_);
return v_res_3734_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = lean_box(0);
v___x_3736_ = l_Lean_interruptExceptionId;
v___x_3737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3735_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg(){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0);
v___x_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v_res_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(lean_object* v_x_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v___y_3751_; uint8_t v___y_3761_; uint16_t v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; uint8_t v___y_3766_; lean_object* v_toCold_3771_; lean_object* v_currRecDepth_3772_; lean_object* v_ref_3773_; uint16_t v_optionFlags_3774_; uint8_t v_suppressElabErrors_3775_; uint8_t v_isRecordingDeps_3776_; lean_object* v_maxRecDepth_3777_; lean_object* v_cancelTk_x3f_3778_; 
v_toCold_3771_ = lean_ctor_get(v___y_3747_, 0);
v_currRecDepth_3772_ = lean_ctor_get(v___y_3747_, 1);
v_ref_3773_ = lean_ctor_get(v___y_3747_, 2);
v_optionFlags_3774_ = lean_ctor_get_uint16(v___y_3747_, sizeof(void*)*3);
v_suppressElabErrors_3775_ = lean_ctor_get_uint8(v___y_3747_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3776_ = lean_ctor_get_uint8(v___y_3747_, sizeof(void*)*3 + 3);
v_maxRecDepth_3777_ = lean_ctor_get(v_toCold_3771_, 3);
v_cancelTk_x3f_3778_ = lean_ctor_get(v_toCold_3771_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3778_) == 1)
{
lean_object* v_val_3784_; uint8_t v___x_3785_; 
v_val_3784_ = lean_ctor_get(v_cancelTk_x3f_3778_, 0);
v___x_3785_ = l_IO_CancelToken_isSet(v_val_3784_);
if (v___x_3785_ == 0)
{
goto v___jp_3779_;
}
else
{
lean_object* v___x_3786_; lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec_ref(v_x_3743_);
v___x_3786_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
goto v___jp_3779_;
}
v___jp_3750_:
{
if (lean_obj_tag(v___y_3751_) == 0)
{
return v___y_3751_;
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_a_3752_ = lean_ctor_get(v___y_3751_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___y_3751_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___y_3751_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___y_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
v___jp_3760_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3767_ = lean_unsigned_to_nat(1u);
v___x_3768_ = lean_nat_add(v___y_3764_, v___x_3767_);
lean_inc_ref(v___y_3763_);
v___x_3769_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3769_, 0, v___y_3763_);
lean_ctor_set(v___x_3769_, 1, v___x_3768_);
lean_ctor_set(v___x_3769_, 2, v___y_3765_);
lean_ctor_set_uint16(v___x_3769_, sizeof(void*)*3, v___y_3762_);
lean_ctor_set_uint8(v___x_3769_, sizeof(void*)*3 + 2, v___y_3766_);
lean_ctor_set_uint8(v___x_3769_, sizeof(void*)*3 + 3, v___y_3761_);
lean_inc(v___y_3748_);
lean_inc(v___y_3746_);
lean_inc_ref(v___y_3745_);
lean_inc(v___y_3744_);
v___x_3770_ = lean_apply_6(v_x_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___x_3769_, v___y_3748_, lean_box(0));
v___y_3751_ = v___x_3770_;
goto v___jp_3750_;
}
v___jp_3779_:
{
lean_object* v___x_3780_; uint8_t v___x_3781_; 
v___x_3780_ = lean_unsigned_to_nat(0u);
v___x_3781_ = lean_nat_dec_eq(v_maxRecDepth_3777_, v___x_3780_);
if (v___x_3781_ == 0)
{
uint8_t v___x_3782_; 
v___x_3782_ = lean_nat_dec_eq(v_currRecDepth_3772_, v_maxRecDepth_3777_);
if (v___x_3782_ == 0)
{
lean_inc(v_ref_3773_);
v___y_3761_ = v_isRecordingDeps_3776_;
v___y_3762_ = v_optionFlags_3774_;
v___y_3763_ = v_toCold_3771_;
v___y_3764_ = v_currRecDepth_3772_;
v___y_3765_ = v_ref_3773_;
v___y_3766_ = v_suppressElabErrors_3775_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3783_; 
lean_dec_ref(v_x_3743_);
lean_inc(v_ref_3773_);
v___x_3783_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3773_);
v___y_3751_ = v___x_3783_;
goto v___jp_3750_;
}
}
else
{
lean_inc(v_ref_3773_);
v___y_3761_ = v_isRecordingDeps_3776_;
v___y_3762_ = v_optionFlags_3774_;
v___y_3763_ = v_toCold_3771_;
v___y_3764_ = v_currRecDepth_3772_;
v___y_3765_ = v_ref_3773_;
v___y_3766_ = v_suppressElabErrors_3775_;
goto v___jp_3760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg___boxed(lean_object* v_x_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v___y_3796_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(lean_object* v_pre_3803_, lean_object* v_post_3804_, size_t v_sz_3805_, size_t v_i_3806_, lean_object* v_bs_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_usize_dec_lt(v_i_3806_, v_sz_3805_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec_ref(v_post_3804_);
lean_dec_ref(v_pre_3803_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_bs_3807_);
return v___x_3815_;
}
else
{
lean_object* v_v_3816_; lean_object* v___x_3817_; lean_object* v_bs_x27_3818_; lean_object* v___x_3819_; 
v_v_3816_ = lean_array_uget(v_bs_3807_, v_i_3806_);
v___x_3817_ = lean_unsigned_to_nat(0u);
v_bs_x27_3818_ = lean_array_uset(v_bs_3807_, v_i_3806_, v___x_3817_);
lean_inc_ref(v_post_3804_);
lean_inc_ref(v_pre_3803_);
v___x_3819_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3803_, v_post_3804_, v_v_3816_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
v___x_3821_ = ((size_t)1ULL);
v___x_3822_ = lean_usize_add(v_i_3806_, v___x_3821_);
v___x_3823_ = lean_array_uset(v_bs_x27_3818_, v_i_3806_, v_a_3820_);
v_i_3806_ = v___x_3822_;
v_bs_3807_ = v___x_3823_;
goto _start;
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v_bs_x27_3818_);
lean_dec_ref(v_post_3804_);
lean_dec_ref(v_pre_3803_);
v_a_3825_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3819_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3819_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_3833_, lean_object* v_post_3834_, lean_object* v_x_3835_, lean_object* v_x_3836_, lean_object* v_x_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
if (lean_obj_tag(v_x_3835_) == 5)
{
lean_object* v_fn_3844_; lean_object* v_arg_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v_fn_3844_ = lean_ctor_get(v_x_3835_, 0);
lean_inc_ref(v_fn_3844_);
v_arg_3845_ = lean_ctor_get(v_x_3835_, 1);
lean_inc_ref(v_arg_3845_);
lean_dec_ref_known(v_x_3835_, 2);
v___x_3846_ = lean_array_set(v_x_3836_, v_x_3837_, v_arg_3845_);
v___x_3847_ = lean_unsigned_to_nat(1u);
v___x_3848_ = lean_nat_sub(v_x_3837_, v___x_3847_);
lean_dec(v_x_3837_);
v_x_3835_ = v_fn_3844_;
v_x_3836_ = v___x_3846_;
v_x_3837_ = v___x_3848_;
goto _start;
}
else
{
lean_object* v___x_3850_; 
lean_dec(v_x_3837_);
lean_inc_ref(v_post_3834_);
lean_inc_ref(v_pre_3833_);
v___x_3850_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3833_, v_post_3834_, v_x_3835_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; size_t v_sz_3852_; size_t v___x_3853_; lean_object* v___x_3854_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v_sz_3852_ = lean_array_size(v_x_3836_);
v___x_3853_ = ((size_t)0ULL);
lean_inc_ref(v_post_3834_);
lean_inc_ref(v_pre_3833_);
v___x_3854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_3833_, v_post_3834_, v_sz_3852_, v___x_3853_, v_x_3836_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref_known(v___x_3854_, 1);
v___x_3856_ = l_Lean_mkAppN(v_a_3851_, v_a_3855_);
lean_dec(v_a_3855_);
v___x_3857_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3833_, v_post_3834_, v___x_3856_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
return v___x_3857_;
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec(v_a_3851_);
lean_dec_ref(v_post_3834_);
lean_dec_ref(v_pre_3833_);
v_a_3858_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3854_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3854_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
lean_dec_ref(v_x_3836_);
lean_dec_ref(v_post_3834_);
lean_dec_ref(v_pre_3833_);
return v___x_3850_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v___x_3866_, lean_object* v_pre_3867_, lean_object* v_e_3868_, lean_object* v_post_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_Core_checkSystem(v___x_3866_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v___x_3877_; 
lean_dec_ref_known(v___x_3876_, 1);
lean_inc_ref(v_pre_3867_);
lean_inc(v___y_3874_);
lean_inc_ref(v___y_3873_);
lean_inc(v___y_3872_);
lean_inc_ref(v___y_3871_);
lean_inc_ref(v_e_3868_);
v___x_3877_ = lean_apply_6(v_pre_3867_, v_e_3868_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, lean_box(0));
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3993_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3880_ = v___x_3877_;
v_isShared_3881_ = v_isSharedCheck_3993_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3877_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3993_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___y_3883_; 
switch(lean_obj_tag(v_a_3878_))
{
case 0:
{
lean_object* v_e_3983_; lean_object* v___x_3985_; 
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_e_3868_);
lean_dec_ref(v_pre_3867_);
v_e_3983_ = lean_ctor_get(v_a_3878_, 0);
lean_inc_ref(v_e_3983_);
lean_dec_ref_known(v_a_3878_, 1);
if (v_isShared_3881_ == 0)
{
lean_ctor_set(v___x_3880_, 0, v_e_3983_);
v___x_3985_ = v___x_3880_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_e_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
case 1:
{
lean_object* v_e_3987_; lean_object* v___x_3988_; 
lean_del_object(v___x_3880_);
lean_dec_ref(v_e_3868_);
v_e_3987_ = lean_ctor_get(v_a_3878_, 0);
lean_inc_ref(v_e_3987_);
lean_dec_ref_known(v_a_3878_, 1);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3988_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_e_3987_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3990_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v___x_3990_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v_a_3989_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3990_;
}
else
{
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3988_;
}
}
default: 
{
lean_object* v_e_x3f_3991_; 
lean_del_object(v___x_3880_);
v_e_x3f_3991_ = lean_ctor_get(v_a_3878_, 0);
lean_inc(v_e_x3f_3991_);
lean_dec_ref_known(v_a_3878_, 1);
if (lean_obj_tag(v_e_x3f_3991_) == 0)
{
v___y_3883_ = v_e_3868_;
goto v___jp_3882_;
}
else
{
lean_object* v_val_3992_; 
lean_dec_ref(v_e_3868_);
v_val_3992_ = lean_ctor_get(v_e_x3f_3991_, 0);
lean_inc(v_val_3992_);
lean_dec_ref_known(v_e_x3f_3991_, 1);
v___y_3883_ = v_val_3992_;
goto v___jp_3882_;
}
}
}
v___jp_3882_:
{
switch(lean_obj_tag(v___y_3883_))
{
case 7:
{
lean_object* v_binderName_3884_; lean_object* v_binderType_3885_; lean_object* v_body_3886_; uint8_t v_binderInfo_3887_; lean_object* v___x_3888_; 
v_binderName_3884_ = lean_ctor_get(v___y_3883_, 0);
v_binderType_3885_ = lean_ctor_get(v___y_3883_, 1);
v_body_3886_ = lean_ctor_get(v___y_3883_, 2);
v_binderInfo_3887_ = lean_ctor_get_uint8(v___y_3883_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3885_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3888_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_binderType_3885_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v_a_3889_; lean_object* v___x_3890_; 
v_a_3889_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_a_3889_);
lean_dec_ref_known(v___x_3888_, 1);
lean_inc_ref(v_body_3886_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3890_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_body_3886_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; size_t v___x_3892_; size_t v___x_3893_; uint8_t v___x_3894_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = lean_ptr_addr(v_binderType_3885_);
v___x_3893_ = lean_ptr_addr(v_a_3889_);
v___x_3894_ = lean_usize_dec_eq(v___x_3892_, v___x_3893_);
if (v___x_3894_ == 0)
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_inc(v_binderName_3884_);
lean_dec_ref_known(v___y_3883_, 3);
v___x_3895_ = l_Lean_Expr_forallE___override(v_binderName_3884_, v_a_3889_, v_a_3891_, v_binderInfo_3887_);
v___x_3896_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3895_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3896_;
}
else
{
size_t v___x_3897_; size_t v___x_3898_; uint8_t v___x_3899_; 
v___x_3897_ = lean_ptr_addr(v_body_3886_);
v___x_3898_ = lean_ptr_addr(v_a_3891_);
v___x_3899_ = lean_usize_dec_eq(v___x_3897_, v___x_3898_);
if (v___x_3899_ == 0)
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_inc(v_binderName_3884_);
lean_dec_ref_known(v___y_3883_, 3);
v___x_3900_ = l_Lean_Expr_forallE___override(v_binderName_3884_, v_a_3889_, v_a_3891_, v_binderInfo_3887_);
v___x_3901_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3900_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3901_;
}
else
{
uint8_t v___x_3902_; 
v___x_3902_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3887_, v_binderInfo_3887_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_inc(v_binderName_3884_);
lean_dec_ref_known(v___y_3883_, 3);
v___x_3903_ = l_Lean_Expr_forallE___override(v_binderName_3884_, v_a_3889_, v_a_3891_, v_binderInfo_3887_);
v___x_3904_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3903_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; 
lean_dec(v_a_3891_);
lean_dec(v_a_3889_);
v___x_3905_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___y_3883_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3905_;
}
}
}
}
else
{
lean_dec(v_a_3889_);
lean_dec_ref_known(v___y_3883_, 3);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3890_;
}
}
else
{
lean_dec_ref_known(v___y_3883_, 3);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3888_;
}
}
case 6:
{
lean_object* v_binderName_3906_; lean_object* v_binderType_3907_; lean_object* v_body_3908_; uint8_t v_binderInfo_3909_; lean_object* v___x_3910_; 
v_binderName_3906_ = lean_ctor_get(v___y_3883_, 0);
v_binderType_3907_ = lean_ctor_get(v___y_3883_, 1);
v_body_3908_ = lean_ctor_get(v___y_3883_, 2);
v_binderInfo_3909_ = lean_ctor_get_uint8(v___y_3883_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3907_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3910_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_binderType_3907_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
lean_inc_ref(v_body_3908_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3912_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_body_3908_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; size_t v___x_3914_; size_t v___x_3915_; uint8_t v___x_3916_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = lean_ptr_addr(v_binderType_3907_);
v___x_3915_ = lean_ptr_addr(v_a_3911_);
v___x_3916_ = lean_usize_dec_eq(v___x_3914_, v___x_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_inc(v_binderName_3906_);
lean_dec_ref_known(v___y_3883_, 3);
v___x_3917_ = l_Lean_Expr_lam___override(v_binderName_3906_, v_a_3911_, v_a_3913_, v_binderInfo_3909_);
v___x_3918_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3917_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3918_;
}
else
{
size_t v___x_3919_; size_t v___x_3920_; uint8_t v___x_3921_; 
v___x_3919_ = lean_ptr_addr(v_body_3908_);
v___x_3920_ = lean_ptr_addr(v_a_3913_);
v___x_3921_ = lean_usize_dec_eq(v___x_3919_, v___x_3920_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
lean_inc(v_binderName_3906_);
lean_dec_ref_known(v___y_3883_, 3);
v___x_3922_ = l_Lean_Expr_lam___override(v_binderName_3906_, v_a_3911_, v_a_3913_, v_binderInfo_3909_);
v___x_3923_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3922_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3923_;
}
else
{
uint8_t v___x_3924_; 
v___x_3924_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3909_, v_binderInfo_3909_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_inc(v_binderName_3906_);
lean_dec_ref_known(v___y_3883_, 3);
v___x_3925_ = l_Lean_Expr_lam___override(v_binderName_3906_, v_a_3911_, v_a_3913_, v_binderInfo_3909_);
v___x_3926_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3925_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3926_;
}
else
{
lean_object* v___x_3927_; 
lean_dec(v_a_3913_);
lean_dec(v_a_3911_);
v___x_3927_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___y_3883_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3927_;
}
}
}
}
else
{
lean_dec(v_a_3911_);
lean_dec_ref_known(v___y_3883_, 3);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3912_;
}
}
else
{
lean_dec_ref_known(v___y_3883_, 3);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3910_;
}
}
case 8:
{
lean_object* v_declName_3928_; lean_object* v_type_3929_; lean_object* v_value_3930_; lean_object* v_body_3931_; uint8_t v_nondep_3932_; lean_object* v___x_3933_; 
v_declName_3928_ = lean_ctor_get(v___y_3883_, 0);
v_type_3929_ = lean_ctor_get(v___y_3883_, 1);
v_value_3930_ = lean_ctor_get(v___y_3883_, 2);
v_body_3931_ = lean_ctor_get(v___y_3883_, 3);
v_nondep_3932_ = lean_ctor_get_uint8(v___y_3883_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3929_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_type_3929_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v___x_3935_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3933_, 1);
lean_inc_ref(v_value_3930_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3935_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_value_3930_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3937_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref_known(v___x_3935_, 1);
lean_inc_ref(v_body_3931_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3937_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_body_3931_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3937_) == 0)
{
lean_object* v_a_3938_; size_t v___x_3939_; size_t v___x_3940_; uint8_t v___x_3941_; 
v_a_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_a_3938_);
lean_dec_ref_known(v___x_3937_, 1);
v___x_3939_ = lean_ptr_addr(v_type_3929_);
v___x_3940_ = lean_ptr_addr(v_a_3934_);
v___x_3941_ = lean_usize_dec_eq(v___x_3939_, v___x_3940_);
if (v___x_3941_ == 0)
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
lean_inc(v_declName_3928_);
lean_dec_ref_known(v___y_3883_, 4);
v___x_3942_ = l_Lean_Expr_letE___override(v_declName_3928_, v_a_3934_, v_a_3936_, v_a_3938_, v_nondep_3932_);
v___x_3943_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3942_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3943_;
}
else
{
size_t v___x_3944_; size_t v___x_3945_; uint8_t v___x_3946_; 
v___x_3944_ = lean_ptr_addr(v_value_3930_);
v___x_3945_ = lean_ptr_addr(v_a_3936_);
v___x_3946_ = lean_usize_dec_eq(v___x_3944_, v___x_3945_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; lean_object* v___x_3948_; 
lean_inc(v_declName_3928_);
lean_dec_ref_known(v___y_3883_, 4);
v___x_3947_ = l_Lean_Expr_letE___override(v_declName_3928_, v_a_3934_, v_a_3936_, v_a_3938_, v_nondep_3932_);
v___x_3948_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3947_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3948_;
}
else
{
size_t v___x_3949_; size_t v___x_3950_; uint8_t v___x_3951_; 
v___x_3949_ = lean_ptr_addr(v_body_3931_);
v___x_3950_ = lean_ptr_addr(v_a_3938_);
v___x_3951_ = lean_usize_dec_eq(v___x_3949_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
lean_inc(v_declName_3928_);
lean_dec_ref_known(v___y_3883_, 4);
v___x_3952_ = l_Lean_Expr_letE___override(v_declName_3928_, v_a_3934_, v_a_3936_, v_a_3938_, v_nondep_3932_);
v___x_3953_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3952_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3953_;
}
else
{
lean_object* v___x_3954_; 
lean_dec(v_a_3938_);
lean_dec(v_a_3936_);
lean_dec(v_a_3934_);
v___x_3954_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___y_3883_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3954_;
}
}
}
}
else
{
lean_dec(v_a_3936_);
lean_dec(v_a_3934_);
lean_dec_ref_known(v___y_3883_, 4);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3937_;
}
}
else
{
lean_dec(v_a_3934_);
lean_dec_ref_known(v___y_3883_, 4);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3935_;
}
}
else
{
lean_dec_ref_known(v___y_3883_, 4);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3933_;
}
}
case 5:
{
lean_object* v_dummy_3955_; lean_object* v_nargs_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_dummy_3955_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3956_ = l_Lean_Expr_getAppNumArgs(v___y_3883_);
lean_inc(v_nargs_3956_);
v___x_3957_ = lean_mk_array(v_nargs_3956_, v_dummy_3955_);
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_nat_sub(v_nargs_3956_, v___x_3958_);
lean_dec(v_nargs_3956_);
v___x_3960_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3867_, v_post_3869_, v___y_3883_, v___x_3957_, v___x_3959_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3960_;
}
case 10:
{
lean_object* v_data_3961_; lean_object* v_expr_3962_; lean_object* v___x_3963_; 
v_data_3961_ = lean_ctor_get(v___y_3883_, 0);
v_expr_3962_ = lean_ctor_get(v___y_3883_, 1);
lean_inc_ref(v_expr_3962_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3963_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_expr_3962_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; size_t v___x_3965_; size_t v___x_3966_; uint8_t v___x_3967_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = lean_ptr_addr(v_expr_3962_);
v___x_3966_ = lean_ptr_addr(v_a_3964_);
v___x_3967_ = lean_usize_dec_eq(v___x_3965_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_inc(v_data_3961_);
lean_dec_ref_known(v___y_3883_, 2);
v___x_3968_ = l_Lean_Expr_mdata___override(v_data_3961_, v_a_3964_);
v___x_3969_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3968_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3969_;
}
else
{
lean_object* v___x_3970_; 
lean_dec(v_a_3964_);
v___x_3970_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___y_3883_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3970_;
}
}
else
{
lean_dec_ref_known(v___y_3883_, 2);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3963_;
}
}
case 11:
{
lean_object* v_typeName_3971_; lean_object* v_idx_3972_; lean_object* v_struct_3973_; lean_object* v___x_3974_; 
v_typeName_3971_ = lean_ctor_get(v___y_3883_, 0);
v_idx_3972_ = lean_ctor_get(v___y_3883_, 1);
v_struct_3973_ = lean_ctor_get(v___y_3883_, 2);
lean_inc_ref(v_struct_3973_);
lean_inc_ref(v_post_3869_);
lean_inc_ref(v_pre_3867_);
v___x_3974_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3867_, v_post_3869_, v_struct_3973_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; size_t v___x_3976_; size_t v___x_3977_; uint8_t v___x_3978_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v___x_3976_ = lean_ptr_addr(v_struct_3973_);
v___x_3977_ = lean_ptr_addr(v_a_3975_);
v___x_3978_ = lean_usize_dec_eq(v___x_3976_, v___x_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_inc(v_idx_3972_);
lean_inc(v_typeName_3971_);
lean_dec_ref_known(v___y_3883_, 3);
v___x_3979_ = l_Lean_Expr_proj___override(v_typeName_3971_, v_idx_3972_, v_a_3975_);
v___x_3980_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___x_3979_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3980_;
}
else
{
lean_object* v___x_3981_; 
lean_dec(v_a_3975_);
v___x_3981_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___y_3883_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3981_;
}
}
else
{
lean_dec_ref_known(v___y_3883_, 3);
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_pre_3867_);
return v___x_3974_;
}
}
default: 
{
lean_object* v___x_3982_; 
v___x_3982_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3867_, v_post_3869_, v___y_3883_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3982_;
}
}
}
}
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_e_3868_);
lean_dec_ref(v_pre_3867_);
v_a_3994_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3877_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3877_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_dec_ref(v_post_3869_);
lean_dec_ref(v_e_3868_);
lean_dec_ref(v_pre_3867_);
v_a_4002_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3876_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3876_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v___x_4010_, lean_object* v_pre_4011_, lean_object* v_e_4012_, lean_object* v_post_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v___x_4010_, v_pre_4011_, v_e_4012_, v_post_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_4021_, lean_object* v_post_4022_, lean_object* v_e_4023_, lean_object* v_a_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
lean_inc(v_a_4024_);
v___x_4030_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4030_, 0, lean_box(0));
lean_closure_set(v___x_4030_, 1, lean_box(0));
lean_closure_set(v___x_4030_, 2, v_a_4024_);
v___x_4031_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_4030_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4063_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4034_ = v___x_4031_;
v_isShared_4035_ = v_isSharedCheck_4063_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4031_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4063_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4036_; 
v___x_4036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___redArg(v_a_4032_, v_e_4023_);
lean_dec(v_a_4032_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v___x_4037_; lean_object* v___f_4038_; lean_object* v___x_4039_; 
lean_del_object(v___x_4034_);
v___x_4037_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
lean_inc_ref(v_e_4023_);
v___f_4038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4038_, 0, v___x_4037_);
lean_closure_set(v___f_4038_, 1, v_pre_4021_);
lean_closure_set(v___f_4038_, 2, v_e_4023_);
lean_closure_set(v___f_4038_, 3, v_post_4022_);
v___x_4039_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v___f_4038_, v_a_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___f_4041_; lean_object* v___x_4042_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc_n(v_a_4040_, 2);
lean_dec_ref_known(v___x_4039_, 1);
lean_inc(v_a_4024_);
v___f_4041_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4041_, 0, v_a_4024_);
lean_closure_set(v___f_4041_, 1, v_e_4023_);
lean_closure_set(v___f_4041_, 2, v_a_4040_);
v___x_4042_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_4041_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; 
v_unused_4050_ = lean_ctor_get(v___x_4042_, 0);
lean_dec(v_unused_4050_);
v___x_4044_ = v___x_4042_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_dec(v___x_4042_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v_a_4040_);
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4040_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_a_4040_);
v_a_4051_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4042_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4042_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_dec_ref(v_e_4023_);
return v___x_4039_;
}
}
else
{
lean_object* v_val_4059_; lean_object* v___x_4061_; 
lean_dec_ref(v_e_4023_);
lean_dec_ref(v_post_4022_);
lean_dec_ref(v_pre_4021_);
v_val_4059_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_val_4059_);
lean_dec_ref_known(v___x_4036_, 1);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v_val_4059_);
v___x_4061_ = v___x_4034_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_val_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec_ref(v_e_4023_);
lean_dec_ref(v_post_4022_);
lean_dec_ref(v_pre_4021_);
v_a_4064_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4031_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4031_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_4072_, lean_object* v_post_4073_, lean_object* v_e_4074_, lean_object* v_a_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v___x_4081_; 
lean_inc_ref(v_post_4073_);
lean_inc(v___y_4079_);
lean_inc_ref(v___y_4078_);
lean_inc(v___y_4077_);
lean_inc_ref(v___y_4076_);
lean_inc_ref(v_e_4074_);
v___x_4081_ = lean_apply_6(v_post_4073_, v_e_4074_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, lean_box(0));
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4100_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4084_ = v___x_4081_;
v_isShared_4085_ = v_isSharedCheck_4100_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4081_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4100_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
switch(lean_obj_tag(v_a_4082_))
{
case 0:
{
lean_object* v_e_4086_; lean_object* v___x_4088_; 
lean_dec_ref(v_e_4074_);
lean_dec_ref(v_post_4073_);
lean_dec_ref(v_pre_4072_);
v_e_4086_ = lean_ctor_get(v_a_4082_, 0);
lean_inc_ref(v_e_4086_);
lean_dec_ref_known(v_a_4082_, 1);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v_e_4086_);
v___x_4088_ = v___x_4084_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_e_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
case 1:
{
lean_object* v_e_4090_; lean_object* v___x_4091_; 
lean_del_object(v___x_4084_);
lean_dec_ref(v_e_4074_);
v_e_4090_ = lean_ctor_get(v_a_4082_, 0);
lean_inc_ref(v_e_4090_);
lean_dec_ref_known(v_a_4082_, 1);
v___x_4091_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4072_, v_post_4073_, v_e_4090_, v_a_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
return v___x_4091_;
}
default: 
{
lean_object* v_e_x3f_4092_; 
lean_dec_ref(v_post_4073_);
lean_dec_ref(v_pre_4072_);
v_e_x3f_4092_ = lean_ctor_get(v_a_4082_, 0);
lean_inc(v_e_x3f_4092_);
lean_dec_ref_known(v_a_4082_, 1);
if (lean_obj_tag(v_e_x3f_4092_) == 0)
{
lean_object* v___x_4094_; 
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v_e_4074_);
v___x_4094_ = v___x_4084_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_e_4074_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
else
{
lean_object* v_val_4096_; lean_object* v___x_4098_; 
lean_dec_ref(v_e_4074_);
v_val_4096_ = lean_ctor_get(v_e_x3f_4092_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v_e_x3f_4092_, 1);
if (v_isShared_4085_ == 0)
{
lean_ctor_set(v___x_4084_, 0, v_val_4096_);
v___x_4098_ = v___x_4084_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_val_4096_);
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
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec_ref(v_e_4074_);
lean_dec_ref(v_post_4073_);
lean_dec_ref(v_pre_4072_);
v_a_4101_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4081_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4081_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4109_, lean_object* v_post_4110_, lean_object* v_e_4111_, lean_object* v_a_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4109_, v_post_4110_, v_e_4111_, v_a_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v_a_4112_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6___boxed(lean_object* v_pre_4119_, lean_object* v_post_4120_, lean_object* v_sz_4121_, lean_object* v_i_4122_, lean_object* v_bs_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
size_t v_sz_boxed_4130_; size_t v_i_boxed_4131_; lean_object* v_res_4132_; 
v_sz_boxed_4130_ = lean_unbox_usize(v_sz_4121_);
lean_dec(v_sz_4121_);
v_i_boxed_4131_ = lean_unbox_usize(v_i_4122_);
lean_dec(v_i_4122_);
v_res_4132_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_4119_, v_post_4120_, v_sz_boxed_4130_, v_i_boxed_4131_, v_bs_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4133_, lean_object* v_post_4134_, lean_object* v_x_4135_, lean_object* v_x_4136_, lean_object* v_x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4133_, v_post_4134_, v_x_4135_, v_x_4136_, v_x_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object* v_pre_4145_, lean_object* v_post_4146_, lean_object* v_e_4147_, lean_object* v_a_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4145_, v_post_4146_, v_e_4147_, v_a_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
lean_dec(v___y_4152_);
lean_dec_ref(v___y_4151_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
lean_dec(v_a_4148_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object* v_input_4155_, lean_object* v_pre_4156_, lean_object* v_post_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v_a_4165_; lean_object* v___x_4166_; 
v___x_4163_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__3);
v___x_4164_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4163_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref(v___x_4164_);
v___x_4166_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4156_, v_post_4157_, v_input_4155_, v_a_4165_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4168_, 0, lean_box(0));
lean_closure_set(v___x_4168_, 1, lean_box(0));
lean_closure_set(v___x_4168_, 2, v_a_4165_);
v___x_4169_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4168_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4169_);
if (v_isSharedCheck_4176_ == 0)
{
lean_object* v_unused_4177_; 
v_unused_4177_ = lean_ctor_get(v___x_4169_, 0);
lean_dec(v_unused_4177_);
v___x_4171_ = v___x_4169_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_dec(v___x_4169_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 0, v_a_4167_);
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4167_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
else
{
lean_dec(v_a_4165_);
return v___x_4166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object* v_input_4178_, lean_object* v_pre_4179_, lean_object* v_post_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4178_, v_pre_4179_, v_post_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
return v_res_4186_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4187_; double v___x_4188_; 
v___x_4187_ = lean_unsigned_to_nat(0u);
v___x_4188_ = lean_float_of_nat(v___x_4187_);
return v___x_4188_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_4192_, lean_object* v_msg_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_ref_4199_; lean_object* v___x_4200_; lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4246_; 
v_ref_4199_ = lean_ctor_get(v___y_4196_, 2);
v___x_4200_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4246_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4246_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4205_; lean_object* v_traceState_4206_; lean_object* v_env_4207_; lean_object* v_nextMacroScope_4208_; lean_object* v_ngen_4209_; lean_object* v_auxDeclNGen_4210_; lean_object* v_cache_4211_; lean_object* v_recordedDeps_4212_; lean_object* v_messages_4213_; lean_object* v_infoState_4214_; lean_object* v_snapshotTasks_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4245_; 
v___x_4205_ = lean_st_ref_take(v___y_4197_);
v_traceState_4206_ = lean_ctor_get(v___x_4205_, 4);
v_env_4207_ = lean_ctor_get(v___x_4205_, 0);
v_nextMacroScope_4208_ = lean_ctor_get(v___x_4205_, 1);
v_ngen_4209_ = lean_ctor_get(v___x_4205_, 2);
v_auxDeclNGen_4210_ = lean_ctor_get(v___x_4205_, 3);
v_cache_4211_ = lean_ctor_get(v___x_4205_, 5);
v_recordedDeps_4212_ = lean_ctor_get(v___x_4205_, 6);
v_messages_4213_ = lean_ctor_get(v___x_4205_, 7);
v_infoState_4214_ = lean_ctor_get(v___x_4205_, 8);
v_snapshotTasks_4215_ = lean_ctor_get(v___x_4205_, 9);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4217_ = v___x_4205_;
v_isShared_4218_ = v_isSharedCheck_4245_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_snapshotTasks_4215_);
lean_inc(v_infoState_4214_);
lean_inc(v_messages_4213_);
lean_inc(v_recordedDeps_4212_);
lean_inc(v_cache_4211_);
lean_inc(v_traceState_4206_);
lean_inc(v_auxDeclNGen_4210_);
lean_inc(v_ngen_4209_);
lean_inc(v_nextMacroScope_4208_);
lean_inc(v_env_4207_);
lean_dec(v___x_4205_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4245_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
uint64_t v_tid_4219_; lean_object* v_traces_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4244_; 
v_tid_4219_ = lean_ctor_get_uint64(v_traceState_4206_, sizeof(void*)*1);
v_traces_4220_ = lean_ctor_get(v_traceState_4206_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v_traceState_4206_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4222_ = v_traceState_4206_;
v_isShared_4223_ = v_isSharedCheck_4244_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_traces_4220_);
lean_dec(v_traceState_4206_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4244_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; double v___x_4226_; uint8_t v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4235_; 
v___x_4224_ = lean_box(0);
v___x_4225_ = lean_box(0);
v___x_4226_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0);
v___x_4227_ = 0;
v___x_4228_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1));
v___x_4229_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4229_, 0, v_cls_4192_);
lean_ctor_set(v___x_4229_, 1, v___x_4225_);
lean_ctor_set(v___x_4229_, 2, v___x_4228_);
lean_ctor_set_float(v___x_4229_, sizeof(void*)*3, v___x_4226_);
lean_ctor_set_float(v___x_4229_, sizeof(void*)*3 + 8, v___x_4226_);
lean_ctor_set_uint8(v___x_4229_, sizeof(void*)*3 + 16, v___x_4227_);
v___x_4230_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2));
v___x_4231_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4229_);
lean_ctor_set(v___x_4231_, 1, v_a_4201_);
lean_ctor_set(v___x_4231_, 2, v___x_4230_);
lean_inc(v_ref_4199_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_ref_4199_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = l_Lean_PersistentArray_push___redArg(v_traces_4220_, v___x_4232_);
if (v_isShared_4223_ == 0)
{
lean_ctor_set(v___x_4222_, 0, v___x_4233_);
v___x_4235_ = v___x_4222_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4233_);
lean_ctor_set_uint64(v_reuseFailAlloc_4243_, sizeof(void*)*1, v_tid_4219_);
v___x_4235_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
lean_object* v___x_4237_; 
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 4, v___x_4235_);
v___x_4237_ = v___x_4217_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_env_4207_);
lean_ctor_set(v_reuseFailAlloc_4242_, 1, v_nextMacroScope_4208_);
lean_ctor_set(v_reuseFailAlloc_4242_, 2, v_ngen_4209_);
lean_ctor_set(v_reuseFailAlloc_4242_, 3, v_auxDeclNGen_4210_);
lean_ctor_set(v_reuseFailAlloc_4242_, 4, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4242_, 5, v_cache_4211_);
lean_ctor_set(v_reuseFailAlloc_4242_, 6, v_recordedDeps_4212_);
lean_ctor_set(v_reuseFailAlloc_4242_, 7, v_messages_4213_);
lean_ctor_set(v_reuseFailAlloc_4242_, 8, v_infoState_4214_);
lean_ctor_set(v_reuseFailAlloc_4242_, 9, v_snapshotTasks_4215_);
v___x_4237_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4238_; lean_object* v___x_4240_; 
v___x_4238_ = lean_st_ref_put(v___y_4197_, v___x_4237_);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4224_);
v___x_4240_ = v___x_4203_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v___x_4224_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_4247_, lean_object* v_msg_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_4247_, v_msg_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4255_, size_t v_i_4256_, lean_object* v_bs_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
uint8_t v___x_4263_; 
v___x_4263_ = lean_usize_dec_lt(v_i_4256_, v_sz_4255_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; 
v___x_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4264_, 0, v_bs_4257_);
return v___x_4264_;
}
else
{
lean_object* v_v_4265_; lean_object* v___x_4266_; lean_object* v_bs_x27_4267_; lean_object* v___x_4268_; 
v_v_4265_ = lean_array_uget(v_bs_4257_, v_i_4256_);
v___x_4266_ = lean_unsigned_to_nat(0u);
v_bs_x27_4267_ = lean_array_uset(v_bs_4257_, v_i_4256_, v___x_4266_);
v___x_4268_ = l_Lean_Elab_WF_mkWfParam(v_v_4265_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; size_t v___x_4270_; size_t v___x_4271_; lean_object* v___x_4272_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4268_, 1);
v___x_4270_ = ((size_t)1ULL);
v___x_4271_ = lean_usize_add(v_i_4256_, v___x_4270_);
v___x_4272_ = lean_array_uset(v_bs_x27_4267_, v_i_4256_, v_a_4269_);
v_i_4256_ = v___x_4271_;
v_bs_4257_ = v___x_4272_;
goto _start;
}
else
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
lean_dec_ref(v_bs_x27_4267_);
v_a_4274_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4268_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4268_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
return v___x_4279_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4282_, lean_object* v_i_4283_, lean_object* v_bs_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
size_t v_sz_boxed_4290_; size_t v_i_boxed_4291_; lean_object* v_res_4292_; 
v_sz_boxed_4290_ = lean_unbox_usize(v_sz_4282_);
lean_dec(v_sz_4282_);
v_i_boxed_4291_ = lean_unbox_usize(v_i_4283_);
lean_dec(v_i_4283_);
v_res_4292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4290_, v_i_boxed_4291_, v_bs_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
return v_res_4292_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4293_; 
v___x_4293_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_4293_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_4295_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__0, &l_Lean_Elab_WF_preprocess___lam__2___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0);
v___x_4296_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
lean_ctor_set(v___x_4296_, 1, v___x_4295_);
lean_ctor_set(v___x_4296_, 2, v___x_4294_);
lean_ctor_set(v___x_4296_, 3, v___x_4294_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
v___x_4297_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
return v___x_4298_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3(void){
_start:
{
lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4299_ = lean_unsigned_to_nat(0u);
v___x_4300_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
lean_ctor_set(v___x_4301_, 1, v___x_4299_);
return v___x_4301_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4302_ = lean_unsigned_to_nat(32u);
v___x_4303_ = lean_mk_empty_array_with_capacity(v___x_4302_);
v___x_4304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4304_, 0, v___x_4303_);
return v___x_4304_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5(void){
_start:
{
size_t v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4305_ = ((size_t)5ULL);
v___x_4306_ = lean_unsigned_to_nat(0u);
v___x_4307_ = lean_unsigned_to_nat(32u);
v___x_4308_ = lean_mk_empty_array_with_capacity(v___x_4307_);
v___x_4309_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4310_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
lean_ctor_set(v___x_4310_, 1, v___x_4308_);
lean_ctor_set(v___x_4310_, 2, v___x_4306_);
lean_ctor_set(v___x_4310_, 3, v___x_4306_);
lean_ctor_set_usize(v___x_4310_, 4, v___x_4305_);
return v___x_4310_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6(void){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4311_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__5, &l_Lean_Elab_WF_preprocess___lam__2___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5);
v___x_4312_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4313_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
lean_ctor_set(v___x_4313_, 2, v___x_4312_);
lean_ctor_set(v___x_4313_, 3, v___x_4311_);
return v___x_4313_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7(void){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4314_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__6, &l_Lean_Elab_WF_preprocess___lam__2___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6);
v___x_4315_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__3, &l_Lean_Elab_WF_preprocess___lam__2___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3);
v___x_4316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
lean_ctor_set(v___x_4316_, 1, v___x_4314_);
return v___x_4316_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__12(void){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4325_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__9));
v___x_4326_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4327_ = l_Lean_Name_append(v___x_4326_, v___x_4325_);
return v___x_4327_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14(void){
_start:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4329_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__13));
v___x_4330_ = l_Lean_stringToMessageData(v___x_4329_);
return v___x_4330_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16(void){
_start:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
v___x_4332_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__15));
v___x_4333_ = l_Lean_stringToMessageData(v___x_4332_);
return v___x_4333_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18(void){
_start:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__17));
v___x_4336_ = l_Lean_stringToMessageData(v___x_4335_);
return v___x_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2(lean_object* v_a_4337_, uint8_t v___x_4338_, lean_object* v___f_4339_, lean_object* v___f_4340_, lean_object* v_xs_4341_, lean_object* v_x_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
size_t v_sz_4348_; size_t v___x_4349_; lean_object* v___x_4350_; 
v_sz_4348_ = lean_array_size(v_xs_4341_);
v___x_4349_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4341_);
v___x_4350_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4348_, v___x_4349_, v_xs_4341_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4352_ = l_Lean_Expr_beta(v_a_4337_, v_a_4351_);
v___x_4353_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__1, &l_Lean_Elab_WF_preprocess___lam__2___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1);
v___x_4354_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_4355_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4353_, v___x_4354_, v___x_4338_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_));
v___x_4358_ = 0;
v___x_4359_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4356_, v___x_4357_, v___x_4358_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
v___x_4361_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_));
v___x_4362_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4360_, v___x_4361_, v___x_4338_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___x_4364_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
v___x_4364_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4343_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4364_) == 0)
{
lean_object* v_a_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc(v_a_4365_);
lean_dec_ref_known(v___x_4364_, 1);
v___x_4366_ = lean_unsigned_to_nat(1u);
v___x_4367_ = lean_mk_empty_array_with_capacity(v___x_4366_);
v___x_4368_ = lean_array_push(v___x_4367_, v_a_4363_);
v___x_4369_ = lean_box(0);
v___x_4370_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__7, &l_Lean_Elab_WF_preprocess___lam__2___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7);
lean_inc_ref(v___x_4352_);
v___x_4371_ = l_Lean_Meta_simp(v___x_4352_, v_a_4365_, v___x_4368_, v___x_4369_, v___x_4370_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v_fst_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4442_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4371_, 1);
v_fst_4373_ = lean_ctor_get(v_a_4372_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4372_);
if (v_isSharedCheck_4442_ == 0)
{
lean_object* v_unused_4443_; 
v_unused_4443_ = lean_ctor_get(v_a_4372_, 1);
lean_dec(v_unused_4443_);
v___x_4375_ = v_a_4372_;
v_isShared_4376_ = v_isSharedCheck_4442_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_fst_4373_);
lean_dec(v_a_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4442_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v_expr_4377_; lean_object* v_proof_x3f_4378_; uint8_t v_cache_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4441_; 
v_expr_4377_ = lean_ctor_get(v_fst_4373_, 0);
v_proof_x3f_4378_ = lean_ctor_get(v_fst_4373_, 1);
v_cache_4379_ = lean_ctor_get_uint8(v_fst_4373_, sizeof(void*)*2);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_fst_4373_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4381_ = v_fst_4373_;
v_isShared_4382_ = v_isSharedCheck_4441_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_proof_x3f_4378_);
lean_inc(v_expr_4377_);
lean_dec(v_fst_4373_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4441_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4383_; 
lean_inc_ref(v_expr_4377_);
v___x_4383_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4377_, v___f_4339_, v___f_4340_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4385_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref_known(v___x_4383_, 1);
v___x_4385_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4384_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v_toCold_4396_; lean_object* v_options_4397_; uint8_t v_hasTrace_4398_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v___x_4385_, 1);
v_toCold_4396_ = lean_ctor_get(v___y_4345_, 0);
v_options_4397_ = lean_ctor_get(v_toCold_4396_, 2);
v_hasTrace_4398_ = lean_ctor_get_uint8(v_options_4397_, sizeof(void*)*1);
if (v_hasTrace_4398_ == 0)
{
lean_dec_ref(v_expr_4377_);
lean_del_object(v___x_4375_);
lean_dec_ref(v___x_4352_);
v___y_4388_ = v___y_4343_;
v___y_4389_ = v___y_4344_;
v___y_4390_ = v___y_4345_;
v___y_4391_ = v___y_4346_;
goto v___jp_4387_;
}
else
{
lean_object* v_inheritedTraceOptions_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; uint8_t v___x_4402_; 
v_inheritedTraceOptions_4399_ = lean_ctor_get(v_toCold_4396_, 11);
v___x_4400_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__9));
v___x_4401_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__12, &l_Lean_Elab_WF_preprocess___lam__2___closed__12_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__12);
v___x_4402_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4399_, v_options_4397_, v___x_4401_);
if (v___x_4402_ == 0)
{
lean_dec_ref(v_expr_4377_);
lean_del_object(v___x_4375_);
lean_dec_ref(v___x_4352_);
v___y_4388_ = v___y_4343_;
v___y_4389_ = v___y_4344_;
v___y_4390_ = v___y_4345_;
v___y_4391_ = v___y_4346_;
goto v___jp_4387_;
}
else
{
lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4406_; 
v___x_4403_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__14, &l_Lean_Elab_WF_preprocess___lam__2___closed__14_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14);
v___x_4404_ = l_Lean_indentExpr(v___x_4352_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set_tag(v___x_4375_, 7);
lean_ctor_set(v___x_4375_, 1, v___x_4404_);
lean_ctor_set(v___x_4375_, 0, v___x_4403_);
v___x_4406_ = v___x_4375_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4403_);
lean_ctor_set(v_reuseFailAlloc_4424_, 1, v___x_4404_);
v___x_4406_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4407_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__16, &l_Lean_Elab_WF_preprocess___lam__2___closed__16_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = l_Lean_indentExpr(v_expr_4377_);
v___x_4410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4408_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__18, &l_Lean_Elab_WF_preprocess___lam__2___closed__18_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4410_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
lean_inc(v_a_4386_);
v___x_4413_ = l_Lean_indentExpr(v_a_4386_);
v___x_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v___x_4400_, v___x_4414_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_dec_ref_known(v___x_4415_, 1);
v___y_4388_ = v___y_4343_;
v___y_4389_ = v___y_4344_;
v___y_4390_ = v___y_4345_;
v___y_4391_ = v___y_4346_;
goto v___jp_4387_;
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec(v_a_4386_);
lean_del_object(v___x_4381_);
lean_dec(v_proof_x3f_4378_);
lean_dec_ref(v_xs_4341_);
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4415_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4415_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
}
}
v___jp_4387_:
{
lean_object* v___x_4393_; 
if (v_isShared_4382_ == 0)
{
lean_ctor_set(v___x_4381_, 0, v_a_4386_);
v___x_4393_ = v___x_4381_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4386_);
lean_ctor_set(v_reuseFailAlloc_4395_, 1, v_proof_x3f_4378_);
lean_ctor_set_uint8(v_reuseFailAlloc_4395_, sizeof(void*)*2, v_cache_4379_);
v___x_4393_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4393_, v_xs_4341_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
lean_dec_ref(v_xs_4341_);
return v___x_4394_;
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_del_object(v___x_4381_);
lean_dec(v_proof_x3f_4378_);
lean_dec_ref(v_expr_4377_);
lean_del_object(v___x_4375_);
lean_dec_ref(v___x_4352_);
lean_dec_ref(v_xs_4341_);
v_a_4425_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4385_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4385_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_del_object(v___x_4381_);
lean_dec(v_proof_x3f_4378_);
lean_dec_ref(v_expr_4377_);
lean_del_object(v___x_4375_);
lean_dec_ref(v___x_4352_);
lean_dec_ref(v_xs_4341_);
v_a_4433_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4383_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4383_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec_ref(v___x_4352_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v___f_4340_);
lean_dec_ref(v___f_4339_);
v_a_4444_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4371_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4371_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_a_4363_);
lean_dec_ref(v___x_4352_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v___f_4340_);
lean_dec_ref(v___f_4339_);
v_a_4452_ = lean_ctor_get(v___x_4364_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4364_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4364_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4364_);
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
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref(v___x_4352_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v___f_4340_);
lean_dec_ref(v___f_4339_);
v_a_4460_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4362_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4362_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v___x_4352_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v___f_4340_);
lean_dec_ref(v___f_4339_);
v_a_4468_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4359_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4359_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref(v___x_4352_);
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v___f_4340_);
lean_dec_ref(v___f_4339_);
v_a_4476_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4355_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4355_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
lean_dec_ref(v_xs_4341_);
lean_dec_ref(v___f_4340_);
lean_dec_ref(v___f_4339_);
lean_dec_ref(v_a_4337_);
v_a_4484_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4350_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4350_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2___boxed(lean_object* v_a_4492_, lean_object* v___x_4493_, lean_object* v___f_4494_, lean_object* v___f_4495_, lean_object* v_xs_4496_, lean_object* v_x_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
uint8_t v___x_13977__boxed_4503_; lean_object* v_res_4504_; 
v___x_13977__boxed_4503_ = lean_unbox(v___x_4493_);
v_res_4504_ = l_Lean_Elab_WF_preprocess___lam__2(v_a_4492_, v___x_13977__boxed_4503_, v___f_4494_, v___f_4495_, v_xs_4496_, v_x_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec_ref(v_x_4497_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_){
_start:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; uint8_t v___x_4515_; 
v___x_4512_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4509_);
v___x_4513_ = l_Lean_wf_preprocess;
v___x_4514_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v___x_4512_, v___x_4513_);
lean_dec_ref(v___x_4512_);
v___x_4515_ = 1;
if (v___x_4514_ == 0)
{
lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4516_ = lean_box(0);
v___x_4517_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4517_, 0, v_e_4506_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
lean_ctor_set_uint8(v___x_4517_, sizeof(void*)*2, v___x_4515_);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
else
{
lean_object* v___f_4519_; lean_object* v___f_4520_; lean_object* v___x_4521_; 
v___f_4519_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___f_4520_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___x_4521_ = l_Lean_Meta_letToHave(v_e_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4523_; lean_object* v___f_4524_; uint8_t v___x_4525_; lean_object* v___x_4526_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc_n(v_a_4522_, 2);
lean_dec_ref_known(v___x_4521_, 1);
v___x_4523_ = lean_box(v___x_4515_);
v___f_4524_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__2___boxed), 11, 4);
lean_closure_set(v___f_4524_, 0, v_a_4522_);
lean_closure_set(v___f_4524_, 1, v___x_4523_);
lean_closure_set(v___f_4524_, 2, v___f_4519_);
lean_closure_set(v___f_4524_, 3, v___f_4520_);
v___x_4525_ = 0;
v___x_4526_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_a_4522_, v___f_4524_, v___x_4525_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
return v___x_4526_;
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
v_a_4527_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v___x_4521_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4521_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_Elab_WF_preprocess(v_e_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4542_, lean_object* v_x_4543_, lean_object* v_x_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4542_, v_x_4543_, v_x_4544_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4551_, lean_object* v_x_4552_, lean_object* v_x_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4551_, v_x_4552_, v_x_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_4560_, lean_object* v_ref_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; 
v___x_4565_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_4561_);
return v___x_4565_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4566_, lean_object* v_ref_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(v_00_u03b1_4566_, v_ref_4567_, v___y_4568_, v___y_4569_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(lean_object* v_00_u03b1_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v___x_4576_; 
v___x_4576_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v___x_4576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(v_00_u03b1_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_00_u03b1_4582_, lean_object* v_x_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v___x_4590_; 
v___x_4590_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_4583_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
return v___x_4590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_00_u03b1_4591_, lean_object* v_x_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_00_u03b1_4591_, v_x_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
lean_dec(v___y_4597_);
lean_dec_ref(v___y_4596_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
return v_res_4599_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_();
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
