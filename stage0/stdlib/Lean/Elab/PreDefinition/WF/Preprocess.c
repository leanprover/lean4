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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__26;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_55_ = l_Lean_Option_register___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(v___x_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
return v_res_58_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_72_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_73_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_74_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_75_ = l_Lean_Meta_registerSimpAttr(v___x_72_, v___x_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_76_;
v_res_76_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
return v_res_78_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_box(0);
v___x_80_ = lean_unsigned_to_nat(16u);
v___x_81_ = lean_mk_array(v___x_80_, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0);
v___x_83_ = lean_unsigned_to_nat(0u);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_82_);
return v___x_84_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2(void){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_85_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3);
v___x_89_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1);
v___x_90_ = 1;
v___x_91_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_88_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*2, v___x_90_);
return v___x_91_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = l_Lean_Elab_WF_wfPreprocessSimpExtension;
v___x_97_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_96_, v_a_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v_maxSteps_100_; lean_object* v_maxDischargeDepth_101_; uint8_t v_contextual_102_; uint8_t v_memoize_103_; uint8_t v_singlePass_104_; uint8_t v_zeta_105_; uint8_t v_beta_106_; uint8_t v_eta_107_; uint8_t v_etaStruct_108_; uint8_t v_iota_109_; uint8_t v_proj_110_; uint8_t v_decide_111_; uint8_t v_arith_112_; uint8_t v_autoUnfold_113_; uint8_t v_failIfUnchanged_114_; uint8_t v_ground_115_; uint8_t v_unfoldPartialApp_116_; uint8_t v_zetaDelta_117_; uint8_t v_index_118_; uint8_t v_implicitDefEqProofs_119_; uint8_t v_zetaUnused_120_; uint8_t v_catchRuntime_121_; uint8_t v_zetaHave_122_; uint8_t v_letToHave_123_; uint8_t v_bitVecOfNat_124_; uint8_t v_warnExponents_125_; uint8_t v_suggestions_126_; lean_object* v_maxSuggestions_127_; uint8_t v_locals_128_; uint8_t v_instances_129_; uint8_t v___x_130_; uint8_t v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_100_ = lean_ctor_get(v___x_99_, 0);
v_maxDischargeDepth_101_ = lean_ctor_get(v___x_99_, 1);
v_contextual_102_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3);
v_memoize_103_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 1);
v_singlePass_104_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 2);
v_zeta_105_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 3);
v_beta_106_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 4);
v_eta_107_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 5);
v_etaStruct_108_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 6);
v_iota_109_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 7);
v_proj_110_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 8);
v_decide_111_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 9);
v_arith_112_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 10);
v_autoUnfold_113_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 11);
v_failIfUnchanged_114_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 13);
v_ground_115_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_116_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 15);
v_zetaDelta_117_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 16);
v_index_118_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_119_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 18);
v_zetaUnused_120_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 19);
v_catchRuntime_121_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 20);
v_zetaHave_122_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 21);
v_letToHave_123_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 22);
v_bitVecOfNat_124_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 24);
v_warnExponents_125_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 25);
v_suggestions_126_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 26);
v_maxSuggestions_127_ = lean_ctor_get(v___x_99_, 2);
v_locals_128_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 27);
v_instances_129_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3 + 28);
v___x_130_ = 1;
v___x_131_ = 0;
lean_inc(v_maxSuggestions_127_);
lean_inc(v_maxDischargeDepth_101_);
lean_inc(v_maxSteps_100_);
v___x_132_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_132_, 0, v_maxSteps_100_);
lean_ctor_set(v___x_132_, 1, v_maxDischargeDepth_101_);
lean_ctor_set(v___x_132_, 2, v_maxSuggestions_127_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3, v_contextual_102_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 1, v_memoize_103_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 2, v_singlePass_104_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 3, v_zeta_105_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 4, v_beta_106_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 5, v_eta_107_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 6, v_etaStruct_108_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 7, v_iota_109_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 8, v_proj_110_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 9, v_decide_111_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 10, v_arith_112_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 11, v_autoUnfold_113_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 12, v___x_130_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 13, v_failIfUnchanged_114_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 14, v_ground_115_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 15, v_unfoldPartialApp_116_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 16, v_zetaDelta_117_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 17, v_index_118_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_119_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 19, v_zetaUnused_120_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 20, v_catchRuntime_121_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 21, v_zetaHave_122_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 22, v_letToHave_123_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 23, v___x_131_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 24, v_bitVecOfNat_124_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 25, v_warnExponents_125_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 26, v_suggestions_126_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 27, v_locals_128_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*3 + 28, v_instances_129_);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = lean_mk_empty_array_with_capacity(v___x_133_);
v___x_135_ = lean_array_push(v___x_134_, v_a_98_);
v___x_136_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4);
v___x_137_ = l_Lean_Options_empty;
v___x_138_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_132_, v___x_135_, v___x_136_, v___x_137_, v_a_92_, v_a_93_, v_a_94_);
return v___x_138_;
}
else
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_a_139_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v___x_97_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_97_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_a_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_92_ = stack[0].m_obj;
lean_object* v_a_93_ = stack[1].m_obj;
lean_object* v_a_94_ = stack[2].m_obj;
lean_object* v_res_147_;
v_res_147_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_92_, v_a_93_, v_a_94_);
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___boxed(lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec_ref(v_a_148_);
return v_res_152_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_153_, v_a_155_, v_a_156_);
return v___x_158_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_153_ = stack[0].m_obj;
lean_object* v_a_154_ = stack[1].m_obj;
lean_object* v_a_155_ = stack[2].m_obj;
lean_object* v_a_156_ = stack[3].m_obj;
lean_object* v_res_159_;
v_res_159_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(v_a_153_, v_a_154_, v_a_155_, v_a_156_);
stack->m_obj
 = v_res_159_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___boxed(lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(v_a_160_, v_a_161_, v_a_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f(lean_object* v_e_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_171_ = lean_unsigned_to_nat(2u);
v___x_172_ = l_Lean_Expr_isAppOfArity(v_e_169_, v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_box(0);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = l_Lean_Expr_appArg_x21(v_e_169_);
v___x_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f___boxed(lean_object* v_e_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Elab_WF_isWfParam_x3f(v_e_176_);
lean_dec_ref(v_e_176_);
return v_res_177_;
}
}
lean_object* l_Lean_Elab_WF_mkWfParam(lean_object* v_e_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_184_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_mk_empty_array_with_capacity(v___x_185_);
v___x_187_ = lean_array_push(v___x_186_, v_e_178_);
v___x_188_ = l_Lean_Meta_mkAppM(v___x_184_, v___x_187_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_188_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_mkWfParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_178_ = stack[0].m_obj;
lean_object* v_a_179_ = stack[1].m_obj;
lean_object* v_a_180_ = stack[2].m_obj;
lean_object* v_a_181_ = stack[3].m_obj;
lean_object* v_a_182_ = stack[4].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Lean_Elab_WF_mkWfParam(v_e_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam___boxed(lean_object* v_e_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Elab_WF_mkWfParam(v_e_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
return v_res_196_;
}
}
lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(lean_object* v_declName_197_, lean_object* v___y_198_){
_start:
{
lean_object* v___x_200_; lean_object* v_env_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_200_ = lean_st_ref_get(v___y_198_);
v_env_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc_ref(v_env_201_);
lean_dec(v___x_200_);
v___x_202_ = l_Lean_Environment_isProjectionFn(v_env_201_, v_declName_197_);
v___x_203_ = lean_box(v___x_202_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT void l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_197_ = stack[0].m_obj;
lean_object* v___y_198_ = stack[1].m_obj;
lean_object* v_res_205_;
v_res_205_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_197_, v___y_198_);
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg___boxed(lean_object* v_declName_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_206_, v___y_207_);
lean_dec(v___y_207_);
return v_res_209_;
}
}
lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(lean_object* v_declName_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_210_, v___y_217_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_210_ = stack[0].m_obj;
lean_object* v___y_211_ = stack[1].m_obj;
lean_object* v___y_212_ = stack[2].m_obj;
lean_object* v___y_213_ = stack[3].m_obj;
lean_object* v___y_214_ = stack[4].m_obj;
lean_object* v___y_215_ = stack[5].m_obj;
lean_object* v___y_216_ = stack[6].m_obj;
lean_object* v___y_217_ = stack[7].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(v_declName_210_, v___y_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___boxed(lean_object* v_declName_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(v_declName_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
return v_res_230_;
}
}
lean_object* l_Lean_Elab_WF_paramProj(lean_object* v_e_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Lean_Expr_isApp(v_e_233_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v_e_233_);
v___x_243_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v_fn_245_; lean_object* v_arg_246_; lean_object* v___x_247_; 
v_fn_245_ = lean_ctor_get(v_e_233_, 0);
lean_inc_ref(v_fn_245_);
v_arg_246_ = lean_ctor_get(v_e_233_, 1);
v___x_247_ = l_Lean_Elab_WF_isWfParam_x3f(v_arg_246_);
if (lean_obj_tag(v___x_247_) == 1)
{
lean_object* v_val_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_291_; 
v_val_248_ = lean_ctor_get(v___x_247_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_247_);
if (v_isSharedCheck_291_ == 0)
{
v___x_250_ = v___x_247_;
v_isShared_251_ = v_isSharedCheck_291_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_val_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_291_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v_f_252_; uint8_t v___x_253_; 
v_f_252_ = l_Lean_Expr_getAppFn(v_e_233_);
lean_dec_ref(v_e_233_);
v___x_253_ = l_Lean_Expr_isConst(v_f_252_);
if (v___x_253_ == 0)
{
lean_object* v___x_254_; lean_object* v___x_256_; 
lean_dec_ref(v_f_252_);
lean_dec(v_val_248_);
lean_dec_ref(v_fn_245_);
v___x_254_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 0);
lean_ctor_set(v___x_250_, 0, v___x_254_);
v___x_256_ = v___x_250_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_290_; 
v___x_258_ = l_Lean_Expr_constName_x21(v_f_252_);
lean_dec_ref(v_f_252_);
v___x_259_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v___x_258_, v_a_240_);
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_290_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_290_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_290_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
uint8_t v___x_264_; 
v___x_264_ = lean_unbox(v_a_260_);
lean_dec(v_a_260_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_267_; 
lean_del_object(v___x_250_);
lean_dec(v_val_248_);
lean_dec_ref(v_fn_245_);
v___x_265_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_265_);
v___x_267_ = v___x_262_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_del_object(v___x_262_);
v___x_269_ = l_Lean_Expr_app___override(v_fn_245_, v_val_248_);
v___x_270_ = l_Lean_Elab_WF_mkWfParam(v___x_269_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_281_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_281_ == 0)
{
v___x_273_ = v___x_270_;
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
else
{
lean_inc(v_a_271_);
lean_dec(v___x_270_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_281_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v___x_276_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set_tag(v___x_250_, 0);
lean_ctor_set(v___x_250_, 0, v_a_271_);
v___x_276_ = v___x_250_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_271_);
v___x_276_ = v_reuseFailAlloc_280_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_278_; 
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_276_);
v___x_278_ = v___x_273_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_del_object(v___x_250_);
v_a_282_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_270_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_270_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
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
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec(v___x_247_);
lean_dec_ref(v_fn_245_);
lean_dec_ref(v_e_233_);
v___x_292_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_paramProj_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_233_ = stack[0].m_obj;
lean_object* v_a_234_ = stack[1].m_obj;
lean_object* v_a_235_ = stack[2].m_obj;
lean_object* v_a_236_ = stack[3].m_obj;
lean_object* v_a_237_ = stack[4].m_obj;
lean_object* v_a_238_ = stack[5].m_obj;
lean_object* v_a_239_ = stack[6].m_obj;
lean_object* v_a_240_ = stack[7].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_Elab_WF_paramProj(v_e_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___boxed(lean_object* v_e_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Elab_WF_paramProj(v_e_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
return v_res_304_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_318_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_319_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_316_, v___x_317_, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_320_;
v_res_320_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_();
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10____boxed(lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_();
return v_res_322_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(lean_object* v_k_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v_b_327_, lean_object* v_c_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
lean_inc(v___y_332_);
lean_inc_ref(v___y_331_);
lean_inc(v___y_330_);
lean_inc_ref(v___y_329_);
lean_inc(v___y_326_);
lean_inc_ref(v___y_325_);
lean_inc(v___y_324_);
v___x_334_ = lean_apply_10(v_k_323_, v_b_327_, v_c_328_, v___y_324_, v___y_325_, v___y_326_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, lean_box(0));
return v___x_334_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_323_ = stack[0].m_obj;
lean_object* v___y_324_ = stack[1].m_obj;
lean_object* v___y_325_ = stack[2].m_obj;
lean_object* v___y_326_ = stack[3].m_obj;
lean_object* v_b_327_ = stack[4].m_obj;
lean_object* v_c_328_ = stack[5].m_obj;
lean_object* v___y_329_ = stack[6].m_obj;
lean_object* v___y_330_ = stack[7].m_obj;
lean_object* v___y_331_ = stack[8].m_obj;
lean_object* v___y_332_ = stack[9].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(v_k_323_, v___y_324_, v___y_325_, v___y_326_, v_b_327_, v_c_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object* v_k_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v_b_340_, lean_object* v_c_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(v_k_336_, v___y_337_, v___y_338_, v___y_339_, v_b_340_, v_c_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
return v_res_347_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object* v_e_348_, lean_object* v_k_349_, uint8_t v_cleanupAnnotations_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v___f_359_; uint8_t v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
lean_inc(v___y_351_);
v___f_359_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_359_, 0, v_k_349_);
lean_closure_set(v___f_359_, 1, v___y_351_);
lean_closure_set(v___f_359_, 2, v___y_352_);
lean_closure_set(v___f_359_, 3, v___y_353_);
v___x_360_ = 1;
v___x_361_ = 0;
v___x_362_ = lean_box(0);
v___x_363_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_348_, v___x_360_, v___x_361_, v___x_360_, v___x_361_, v___x_362_, v___f_359_, v_cleanupAnnotations_350_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
if (lean_obj_tag(v___x_363_) == 0)
{
return v___x_363_;
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_363_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_348_ = stack[0].m_obj;
lean_object* v_k_349_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_350_ = stack[2].m_num;
lean_object* v___y_351_ = stack[3].m_obj;
lean_object* v___y_352_ = stack[4].m_obj;
lean_object* v___y_353_ = stack[5].m_obj;
lean_object* v___y_354_ = stack[6].m_obj;
lean_object* v___y_355_ = stack[7].m_obj;
lean_object* v___y_356_ = stack[8].m_obj;
lean_object* v___y_357_ = stack[9].m_obj;
lean_object* v_res_372_;
v_res_372_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_348_, v_k_349_, v_cleanupAnnotations_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
stack->m_obj
 = v_res_372_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___boxed(lean_object* v_e_373_, lean_object* v_k_374_, lean_object* v_cleanupAnnotations_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_384_; lean_object* v_res_385_; 
v_cleanupAnnotations_boxed_384_ = lean_unbox(v_cleanupAnnotations_375_);
v_res_385_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_373_, v_k_374_, v_cleanupAnnotations_boxed_384_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
return v_res_385_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_object* v_00_u03b1_386_, lean_object* v_e_387_, lean_object* v_k_388_, uint8_t v_cleanupAnnotations_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_387_, v_k_388_, v_cleanupAnnotations_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
return v___x_398_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_387_ = stack[1].m_obj;
lean_object* v_k_388_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_389_ = stack[3].m_num;
lean_object* v___y_390_ = stack[4].m_obj;
lean_object* v___y_391_ = stack[5].m_obj;
lean_object* v___y_392_ = stack[6].m_obj;
lean_object* v___y_393_ = stack[7].m_obj;
lean_object* v___y_394_ = stack[8].m_obj;
lean_object* v___y_395_ = stack[9].m_obj;
lean_object* v___y_396_ = stack[10].m_obj;
lean_object* v_res_399_;
v_res_399_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_box(0), v_e_387_, v_k_388_, v_cleanupAnnotations_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
stack->m_obj
 = v_res_399_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___boxed(lean_object* v_00_u03b1_400_, lean_object* v_e_401_, lean_object* v_k_402_, lean_object* v_cleanupAnnotations_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_412_; lean_object* v_res_413_; 
v_cleanupAnnotations_boxed_412_ = lean_unbox(v_cleanupAnnotations_403_);
v_res_413_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(v_00_u03b1_400_, v_e_401_, v_k_402_, v_cleanupAnnotations_boxed_412_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
return v_res_413_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_417_ == 0)
{
return v_bs_416_;
}
else
{
lean_object* v_v_418_; lean_object* v___x_419_; lean_object* v_bs_x27_420_; lean_object* v___y_422_; lean_object* v___x_427_; 
v_v_418_ = lean_array_uget(v_bs_416_, v_i_415_);
v___x_419_ = lean_unsigned_to_nat(0u);
v_bs_x27_420_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_419_);
v___x_427_ = l_Lean_Elab_WF_isWfParam_x3f(v_v_418_);
if (lean_obj_tag(v___x_427_) == 0)
{
v___y_422_ = v_v_418_;
goto v___jp_421_;
}
else
{
lean_object* v_val_428_; 
lean_dec(v_v_418_);
v_val_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_val_428_);
lean_dec_ref_known(v___x_427_, 1);
v___y_422_ = v_val_428_;
goto v___jp_421_;
}
v___jp_421_:
{
size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_add(v_i_415_, v___x_423_);
v___x_425_ = lean_array_uset(v_bs_x27_420_, v_i_415_, v___y_422_);
v_i_415_ = v___x_424_;
v_bs_416_ = v___x_425_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_414_ = stack[0].m_num;
size_t v_i_415_ = stack[1].m_num;
lean_object* v_bs_416_ = stack[2].m_obj;
lean_object* v_res_429_;
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_414_, v_i_415_, v_bs_416_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___boxed(lean_object* v_sz_430_, lean_object* v_i_431_, lean_object* v_bs_432_){
_start:
{
size_t v_sz_boxed_433_; size_t v_i_boxed_434_; lean_object* v_res_435_; 
v_sz_boxed_433_ = lean_unbox_usize(v_sz_430_);
lean_dec(v_sz_430_);
v_i_boxed_434_ = lean_unbox_usize(v_i_431_);
lean_dec(v_i_431_);
v_res_435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_boxed_433_, v_i_boxed_434_, v_bs_432_);
return v_res_435_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(lean_object* v_msgData_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
lean_object* v___x_442_; lean_object* v_env_443_; uint8_t v___x_444_; lean_object* v_env_445_; lean_object* v___x_446_; lean_object* v_toCold_447_; lean_object* v_mctx_448_; lean_object* v_lctx_449_; lean_object* v_options_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_442_ = lean_st_ref_get(v___y_440_);
v_env_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc_ref(v_env_443_);
lean_dec(v___x_442_);
v___x_444_ = 0;
v_env_445_ = l_Lean_Environment_setRecordingDeps(v_env_443_, v___x_444_);
v___x_446_ = lean_st_ref_get(v___y_438_);
v_toCold_447_ = lean_ctor_get(v___y_439_, 0);
v_mctx_448_ = lean_ctor_get(v___x_446_, 0);
lean_inc_ref(v_mctx_448_);
lean_dec(v___x_446_);
v_lctx_449_ = lean_ctor_get(v___y_437_, 2);
v_options_450_ = lean_ctor_get(v_toCold_447_, 2);
lean_inc_ref(v_options_450_);
lean_inc_ref(v_lctx_449_);
v___x_451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_451_, 0, v_env_445_);
lean_ctor_set(v___x_451_, 1, v_mctx_448_);
lean_ctor_set(v___x_451_, 2, v_lctx_449_);
lean_ctor_set(v___x_451_, 3, v_options_450_);
v___x_452_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_msgData_436_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_436_ = stack[0].m_obj;
lean_object* v___y_437_ = stack[1].m_obj;
lean_object* v___y_438_ = stack[2].m_obj;
lean_object* v___y_439_ = stack[3].m_obj;
lean_object* v___y_440_ = stack[4].m_obj;
lean_object* v_res_454_;
v_res_454_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msgData_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
stack->m_obj
 = v_res_454_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16___boxed(lean_object* v_msgData_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msgData_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_461_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_ref_468_; lean_object* v___x_469_; lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_478_; 
v_ref_468_ = lean_ctor_get(v___y_465_, 2);
v___x_469_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_478_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_476_; 
lean_inc(v_ref_468_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_ref_468_);
lean_ctor_set(v___x_474_, 1, v_a_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 1);
lean_ctor_set(v___x_472_, 0, v___x_474_);
v___x_476_ = v___x_472_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_462_ = stack[0].m_obj;
lean_object* v___y_463_ = stack[1].m_obj;
lean_object* v___y_464_ = stack[2].m_obj;
lean_object* v___y_465_ = stack[3].m_obj;
lean_object* v___y_466_ = stack[4].m_obj;
lean_object* v_res_479_;
v_res_479_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
stack->m_obj
 = v_res_479_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg___boxed(lean_object* v_msg_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
return v_res_486_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(lean_object* v_ref_487_, lean_object* v_msg_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_toCold_497_; lean_object* v_currRecDepth_498_; lean_object* v_ref_499_; uint16_t v_optionFlags_500_; uint8_t v_suppressElabErrors_501_; uint8_t v_isRecordingDeps_502_; lean_object* v_ref_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_toCold_497_ = lean_ctor_get(v___y_494_, 0);
v_currRecDepth_498_ = lean_ctor_get(v___y_494_, 1);
v_ref_499_ = lean_ctor_get(v___y_494_, 2);
v_optionFlags_500_ = lean_ctor_get_uint16(v___y_494_, sizeof(void*)*3);
v_suppressElabErrors_501_ = lean_ctor_get_uint8(v___y_494_, sizeof(void*)*3 + 2);
v_isRecordingDeps_502_ = lean_ctor_get_uint8(v___y_494_, sizeof(void*)*3 + 3);
v_ref_503_ = l_Lean_replaceRef(v_ref_487_, v_ref_499_);
lean_inc(v_currRecDepth_498_);
lean_inc_ref(v_toCold_497_);
v___x_504_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_504_, 0, v_toCold_497_);
lean_ctor_set(v___x_504_, 1, v_currRecDepth_498_);
lean_ctor_set(v___x_504_, 2, v_ref_503_);
lean_ctor_set_uint16(v___x_504_, sizeof(void*)*3, v_optionFlags_500_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3 + 2, v_suppressElabErrors_501_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*3 + 3, v_isRecordingDeps_502_);
v___x_505_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_488_, v___y_492_, v___y_493_, v___x_504_, v___y_495_);
lean_dec_ref_known(v___x_504_, 3);
return v___x_505_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_487_ = stack[0].m_obj;
lean_object* v_msg_488_ = stack[1].m_obj;
lean_object* v___y_489_ = stack[2].m_obj;
lean_object* v___y_490_ = stack[3].m_obj;
lean_object* v___y_491_ = stack[4].m_obj;
lean_object* v___y_492_ = stack[5].m_obj;
lean_object* v___y_493_ = stack[6].m_obj;
lean_object* v___y_494_ = stack[7].m_obj;
lean_object* v___y_495_ = stack[8].m_obj;
lean_object* v_res_506_;
v_res_506_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_487_, v_msg_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_507_, lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_507_, v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec(v_ref_507_);
return v_res_517_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
lean_ctor_set(v___x_523_, 2, v___x_522_);
lean_ctor_set(v___x_523_, 3, v___x_522_);
lean_ctor_set(v___x_523_, 4, v___x_521_);
lean_ctor_set(v___x_523_, 5, v___x_521_);
lean_ctor_set(v___x_523_, 6, v___x_521_);
lean_ctor_set(v___x_523_, 7, v___x_521_);
lean_ctor_set(v___x_523_, 8, v___x_521_);
lean_ctor_set(v___x_523_, 9, v___x_521_);
lean_ctor_set(v___x_523_, 10, v___x_521_);
lean_ctor_set(v___x_523_, 11, v___x_520_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = lean_unsigned_to_nat(32u);
v___x_525_ = lean_mk_empty_array_with_capacity(v___x_524_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_527_ = ((size_t)5ULL);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = lean_unsigned_to_nat(32u);
v___x_530_ = lean_mk_empty_array_with_capacity(v___x_529_);
v___x_531_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_532_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v___x_530_);
lean_ctor_set(v___x_532_, 2, v___x_528_);
lean_ctor_set(v___x_532_, 3, v___x_528_);
lean_ctor_set_usize(v___x_532_, 4, v___x_527_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = lean_box(1);
v___x_534_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_535_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
lean_ctor_set(v___x_536_, 1, v___x_534_);
lean_ctor_set(v___x_536_, 2, v___x_533_);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_539_ = l_Lean_stringToMessageData(v___x_538_);
return v___x_539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_542_ = l_Lean_stringToMessageData(v___x_541_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_545_ = l_Lean_stringToMessageData(v___x_544_);
return v___x_545_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_553_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_554_ = l_Lean_stringToMessageData(v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__20(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19));
v___x_560_ = l_Lean_stringToMessageData(v___x_559_);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__22(void){
_start:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__21));
v___x_563_ = l_Lean_stringToMessageData(v___x_562_);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__24(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__23));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__26(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__25));
v___x_569_ = l_Lean_stringToMessageData(v___x_568_);
return v___x_569_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_570_, lean_object* v_declHint_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_env_576_; uint8_t v___x_577_; 
v___x_574_ = lean_box(0);
v___x_575_ = lean_st_ref_get(v___y_572_);
v_env_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_env_576_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_Name_isAnonymous(v_declHint_571_);
if (v___x_577_ == 0)
{
uint8_t v_isExporting_578_; 
v_isExporting_578_ = lean_ctor_get_uint8(v_env_576_, sizeof(void*)*13);
if (v_isExporting_578_ == 0)
{
lean_object* v___x_579_; 
lean_dec_ref(v_env_576_);
lean_dec(v_declHint_571_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v_msg_570_);
return v___x_579_;
}
else
{
lean_object* v___x_580_; uint8_t v___x_581_; 
lean_inc_ref(v_env_576_);
v___x_580_ = l_Lean_Environment_setExporting(v_env_576_, v___x_577_);
lean_inc(v_declHint_571_);
lean_inc_ref(v___x_580_);
v___x_581_ = l_Lean_Environment_contains(v___x_580_, v_declHint_571_, v_isExporting_578_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; 
lean_dec_ref(v___x_580_);
lean_dec_ref(v_env_576_);
lean_dec(v_declHint_571_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v_msg_570_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_c_588_; lean_object* v___x_589_; 
v___x_583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_585_ = l_Lean_Options_empty;
v___x_586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_586_, 0, v___x_580_);
lean_ctor_set(v___x_586_, 1, v___x_583_);
lean_ctor_set(v___x_586_, 2, v___x_584_);
lean_ctor_set(v___x_586_, 3, v___x_585_);
lean_inc(v_declHint_571_);
v___x_587_ = l_Lean_MessageData_ofConstName(v_declHint_571_, v___x_577_);
v_c_588_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_588_, 0, v___x_586_);
lean_ctor_set(v_c_588_, 1, v___x_587_);
v___x_589_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_576_, v_declHint_571_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref(v_env_576_);
lean_dec(v_declHint_571_);
v___x_590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v_c_588_);
v___x_592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_MessageData_note(v___x_593_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v_msg_570_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
else
{
lean_object* v_val_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_653_; 
v_val_597_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_653_ == 0)
{
v___x_599_ = v___x_589_;
v_isShared_600_ = v_isSharedCheck_653_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_val_597_);
lean_dec(v___x_589_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_653_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v_modules_602_; lean_object* v_moduleNames_603_; lean_object* v_mod_604_; uint8_t v___y_606_; uint8_t v___x_636_; 
v___x_601_ = l_Lean_Environment_header(v_env_576_);
lean_dec_ref(v_env_576_);
v_modules_602_ = lean_ctor_get(v___x_601_, 3);
lean_inc_ref(v_modules_602_);
v_moduleNames_603_ = lean_ctor_get(v___x_601_, 4);
lean_inc_ref(v_moduleNames_603_);
lean_dec_ref(v___x_601_);
v_mod_604_ = lean_array_get(v___x_574_, v_moduleNames_603_, v_val_597_);
lean_dec_ref(v_moduleNames_603_);
v___x_636_ = l_Lean_isPrivateName(v_declHint_571_);
lean_dec(v_declHint_571_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_array_get_size(v_modules_602_);
v___x_638_ = lean_nat_dec_lt(v_val_597_, v___x_637_);
if (v___x_638_ == 0)
{
lean_dec_ref(v_modules_602_);
lean_dec(v_val_597_);
v___y_606_ = v___x_636_;
goto v___jp_605_;
}
else
{
lean_object* v___x_639_; lean_object* v_toImport_640_; uint8_t v_isExported_641_; 
v___x_639_ = lean_array_fget(v_modules_602_, v_val_597_);
lean_dec(v_val_597_);
lean_dec_ref(v_modules_602_);
v_toImport_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc_ref(v_toImport_640_);
lean_dec(v___x_639_);
v_isExported_641_ = lean_ctor_get_uint8(v_toImport_640_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_640_);
v___y_606_ = v_isExported_641_;
goto v___jp_605_;
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref(v_modules_602_);
lean_del_object(v___x_599_);
lean_dec(v_val_597_);
v___x_642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v_c_588_);
v___x_644_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__24);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_643_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
v___x_646_ = l_Lean_MessageData_ofName(v_mod_604_);
v___x_647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_645_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__26);
v___x_649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_MessageData_note(v___x_649_);
v___x_651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_651_, 0, v_msg_570_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
v___jp_605_:
{
if (v___y_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_c_588_);
v___x_609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_MessageData_ofName(v_mod_604_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = l_Lean_MessageData_note(v___x_614_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v_msg_570_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 0);
lean_ctor_set(v___x_599_, 0, v___x_616_);
v___x_618_ = v___x_599_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
lean_ctor_set(v___x_621_, 1, v_c_588_);
v___x_622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_621_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v___x_624_ = l_Lean_MessageData_ofName(v_mod_604_);
lean_inc_ref(v___x_624_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__20);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_624_);
v___x_629_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__22);
v___x_630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_MessageData_note(v___x_630_);
v___x_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_632_, 0, v_msg_570_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 0);
lean_ctor_set(v___x_599_, 0, v___x_632_);
v___x_634_ = v___x_599_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
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
lean_object* v___x_654_; 
lean_dec_ref(v_env_576_);
lean_dec(v_declHint_571_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_msg_570_);
return v___x_654_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_570_ = stack[0].m_obj;
lean_object* v_declHint_571_ = stack[1].m_obj;
lean_object* v___y_572_ = stack[2].m_obj;
lean_object* v_res_655_;
v_res_655_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_570_, v_declHint_571_, v___y_572_);
stack->m_obj
 = v_res_655_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_656_, lean_object* v_declHint_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_656_, v_declHint_657_, v___y_658_);
lean_dec(v___y_658_);
return v_res_660_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object* v_msg_661_, lean_object* v_declHint_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_681_; 
v___x_671_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_661_, v_declHint_662_, v___y_669_);
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v___x_676_ = l_Lean_unknownIdentifierMessageTag;
v___x_677_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v_a_672_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_677_);
v___x_679_ = v___x_674_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_661_ = stack[0].m_obj;
lean_object* v_declHint_662_ = stack[1].m_obj;
lean_object* v___y_663_ = stack[2].m_obj;
lean_object* v___y_664_ = stack[3].m_obj;
lean_object* v___y_665_ = stack[4].m_obj;
lean_object* v___y_666_ = stack[5].m_obj;
lean_object* v___y_667_ = stack[6].m_obj;
lean_object* v___y_668_ = stack[7].m_obj;
lean_object* v___y_669_ = stack[8].m_obj;
lean_object* v_res_682_;
v_res_682_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_661_, v_declHint_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
stack->m_obj
 = v_res_682_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_683_, lean_object* v_declHint_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_683_, v_declHint_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
return v_res_693_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_ref_694_, lean_object* v_msg_695_, lean_object* v_declHint_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v___x_705_; lean_object* v_a_706_; lean_object* v___x_707_; 
v___x_705_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_695_, v_declHint_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref(v___x_705_);
v___x_707_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_694_, v_a_706_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
return v___x_707_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_694_ = stack[0].m_obj;
lean_object* v_msg_695_ = stack[1].m_obj;
lean_object* v_declHint_696_ = stack[2].m_obj;
lean_object* v___y_697_ = stack[3].m_obj;
lean_object* v___y_698_ = stack[4].m_obj;
lean_object* v___y_699_ = stack[5].m_obj;
lean_object* v___y_700_ = stack[6].m_obj;
lean_object* v___y_701_ = stack[7].m_obj;
lean_object* v___y_702_ = stack[8].m_obj;
lean_object* v___y_703_ = stack[9].m_obj;
lean_object* v_res_708_;
v_res_708_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_694_, v_msg_695_, v_declHint_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_ref_709_, lean_object* v_msg_710_, lean_object* v_declHint_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_709_, v_msg_710_, v_declHint_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec(v_ref_709_);
return v_res_720_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0));
v___x_723_ = l_Lean_stringToMessageData(v___x_722_);
return v___x_723_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2));
v___x_726_ = l_Lean_stringToMessageData(v___x_725_);
return v___x_726_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_ref_727_, lean_object* v_constName_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_737_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_738_ = 0;
lean_inc(v_constName_728_);
v___x_739_ = l_Lean_MessageData_ofConstName(v_constName_728_, v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_727_, v___x_742_, v_constName_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_743_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_727_ = stack[0].m_obj;
lean_object* v_constName_728_ = stack[1].m_obj;
lean_object* v___y_729_ = stack[2].m_obj;
lean_object* v___y_730_ = stack[3].m_obj;
lean_object* v___y_731_ = stack[4].m_obj;
lean_object* v___y_732_ = stack[5].m_obj;
lean_object* v___y_733_ = stack[6].m_obj;
lean_object* v___y_734_ = stack[7].m_obj;
lean_object* v___y_735_ = stack[8].m_obj;
lean_object* v_res_744_;
v_res_744_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_727_, v_constName_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_ref_745_, lean_object* v_constName_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_745_, v_constName_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec(v_ref_745_);
return v_res_755_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_ref_765_; lean_object* v___x_766_; 
v_ref_765_ = lean_ctor_get(v___y_762_, 2);
v___x_766_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_765_, v_constName_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
return v___x_766_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_756_ = stack[0].m_obj;
lean_object* v___y_757_ = stack[1].m_obj;
lean_object* v___y_758_ = stack[2].m_obj;
lean_object* v___y_759_ = stack[3].m_obj;
lean_object* v___y_760_ = stack[4].m_obj;
lean_object* v___y_761_ = stack[5].m_obj;
lean_object* v___y_762_ = stack[6].m_obj;
lean_object* v___y_763_ = stack[7].m_obj;
lean_object* v_res_767_;
v_res_767_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
return v_res_777_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object* v_constName_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v_env_788_; uint8_t v___x_789_; lean_object* v___x_790_; 
v___x_787_ = lean_st_ref_get(v___y_785_);
v_env_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_env_788_);
lean_dec(v___x_787_);
v___x_789_ = 0;
lean_inc(v_constName_778_);
v___x_790_ = l_Lean_Environment_find_x3f(v_env_788_, v_constName_778_, v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
return v___x_791_;
}
else
{
lean_object* v_val_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec(v_constName_778_);
v_val_792_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_790_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_val_792_);
lean_dec(v___x_790_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
lean_ctor_set_tag(v___x_794_, 0);
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_val_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_778_ = stack[0].m_obj;
lean_object* v___y_779_ = stack[1].m_obj;
lean_object* v___y_780_ = stack[2].m_obj;
lean_object* v___y_781_ = stack[3].m_obj;
lean_object* v___y_782_ = stack[4].m_obj;
lean_object* v___y_783_ = stack[5].m_obj;
lean_object* v___y_784_ = stack[6].m_obj;
lean_object* v___y_785_ = stack[7].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object* v_constName_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
return v_res_810_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_instMonadEIO___redArg();
return v___x_811_;
}
}
lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object* v_msg_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v_toApplicative_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_891_; 
v___x_825_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0);
v___x_826_ = l_StateRefT_x27_instMonad___redArg(v___x_825_);
v_toApplicative_827_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_891_ == 0)
{
lean_object* v_unused_892_; 
v_unused_892_ = lean_ctor_get(v___x_826_, 1);
lean_dec(v_unused_892_);
v___x_829_ = v___x_826_;
v_isShared_830_ = v_isSharedCheck_891_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_toApplicative_827_);
lean_dec(v___x_826_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_891_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v_toFunctor_831_; lean_object* v_toSeq_832_; lean_object* v_toSeqLeft_833_; lean_object* v_toSeqRight_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_889_; 
v_toFunctor_831_ = lean_ctor_get(v_toApplicative_827_, 0);
v_toSeq_832_ = lean_ctor_get(v_toApplicative_827_, 2);
v_toSeqLeft_833_ = lean_ctor_get(v_toApplicative_827_, 3);
v_toSeqRight_834_ = lean_ctor_get(v_toApplicative_827_, 4);
v_isSharedCheck_889_ = !lean_is_exclusive(v_toApplicative_827_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v_toApplicative_827_, 1);
lean_dec(v_unused_890_);
v___x_836_ = v_toApplicative_827_;
v_isShared_837_ = v_isSharedCheck_889_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_toSeqRight_834_);
lean_inc(v_toSeqLeft_833_);
lean_inc(v_toSeq_832_);
lean_inc(v_toFunctor_831_);
lean_dec(v_toApplicative_827_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_889_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___f_838_; lean_object* v___f_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___f_843_; lean_object* v___f_844_; lean_object* v___f_845_; lean_object* v___x_847_; 
v___f_838_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1));
v___f_839_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_831_);
v___f_840_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_840_, 0, v_toFunctor_831_);
v___f_841_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_841_, 0, v_toFunctor_831_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___f_840_);
lean_ctor_set(v___x_842_, 1, v___f_841_);
v___f_843_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_843_, 0, v_toSeqRight_834_);
v___f_844_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_844_, 0, v_toSeqLeft_833_);
v___f_845_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_845_, 0, v_toSeq_832_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 4, v___f_843_);
lean_ctor_set(v___x_836_, 3, v___f_844_);
lean_ctor_set(v___x_836_, 2, v___f_845_);
lean_ctor_set(v___x_836_, 1, v___f_838_);
lean_ctor_set(v___x_836_, 0, v___x_842_);
v___x_847_ = v___x_836_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___f_838_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v___f_845_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___f_844_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v___f_843_);
v___x_847_ = v_reuseFailAlloc_888_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
lean_object* v___x_849_; 
if (v_isShared_830_ == 0)
{
lean_ctor_set(v___x_829_, 1, v___f_839_);
lean_ctor_set(v___x_829_, 0, v___x_847_);
v___x_849_ = v___x_829_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v___f_839_);
v___x_849_ = v_reuseFailAlloc_887_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v_toApplicative_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_885_; 
v___x_850_ = l_StateRefT_x27_instMonad___redArg(v___x_849_);
v_toApplicative_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_850_, 1);
lean_dec(v_unused_886_);
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_885_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_toApplicative_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_885_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_toFunctor_855_; lean_object* v_toSeq_856_; lean_object* v_toSeqLeft_857_; lean_object* v_toSeqRight_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_883_; 
v_toFunctor_855_ = lean_ctor_get(v_toApplicative_851_, 0);
v_toSeq_856_ = lean_ctor_get(v_toApplicative_851_, 2);
v_toSeqLeft_857_ = lean_ctor_get(v_toApplicative_851_, 3);
v_toSeqRight_858_ = lean_ctor_get(v_toApplicative_851_, 4);
v_isSharedCheck_883_ = !lean_is_exclusive(v_toApplicative_851_);
if (v_isSharedCheck_883_ == 0)
{
lean_object* v_unused_884_; 
v_unused_884_ = lean_ctor_get(v_toApplicative_851_, 1);
lean_dec(v_unused_884_);
v___x_860_ = v_toApplicative_851_;
v_isShared_861_ = v_isSharedCheck_883_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_toSeqRight_858_);
lean_inc(v_toSeqLeft_857_);
lean_inc(v_toSeq_856_);
lean_inc(v_toFunctor_855_);
lean_dec(v_toApplicative_851_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_883_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___f_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___x_871_; 
v___f_862_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3));
v___f_863_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_855_);
v___f_864_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_864_, 0, v_toFunctor_855_);
v___f_865_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_865_, 0, v_toFunctor_855_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___f_864_);
lean_ctor_set(v___x_866_, 1, v___f_865_);
v___f_867_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_867_, 0, v_toSeqRight_858_);
v___f_868_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_868_, 0, v_toSeqLeft_857_);
v___f_869_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_869_, 0, v_toSeq_856_);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 4, v___f_867_);
lean_ctor_set(v___x_860_, 3, v___f_868_);
lean_ctor_set(v___x_860_, 2, v___f_869_);
lean_ctor_set(v___x_860_, 1, v___f_862_);
lean_ctor_set(v___x_860_, 0, v___x_866_);
v___x_871_ = v___x_860_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v___f_862_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v___f_869_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v___f_868_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v___f_867_);
v___x_871_ = v_reuseFailAlloc_882_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___f_863_);
lean_ctor_set(v___x_853_, 0, v___x_871_);
v___x_873_ = v___x_853_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_871_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___f_863_);
v___x_873_ = v_reuseFailAlloc_881_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_13046__overap_879_; lean_object* v___x_880_; 
v___x_874_ = l_StateRefT_x27_instMonad___redArg(v___x_873_);
v___x_875_ = l_ReaderT_instMonad___redArg(v___x_874_);
v___x_876_ = l_ReaderT_instMonad___redArg(v___x_875_);
v___x_877_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_878_ = l_instInhabitedOfMonad___redArg(v___x_876_, v___x_877_);
v___x_13046__overap_879_ = lean_panic_fn_borrowed(v___x_878_, v_msg_816_);
lean_dec(v___x_878_);
lean_inc(v___y_823_);
lean_inc_ref(v___y_822_);
lean_inc(v___y_821_);
lean_inc_ref(v___y_820_);
lean_inc(v___y_819_);
lean_inc_ref(v___y_818_);
lean_inc(v___y_817_);
v___x_880_ = lean_apply_8(v___x_13046__overap_879_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, lean_box(0));
return v___x_880_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_816_ = stack[0].m_obj;
lean_object* v___y_817_ = stack[1].m_obj;
lean_object* v___y_818_ = stack[2].m_obj;
lean_object* v___y_819_ = stack[3].m_obj;
lean_object* v___y_820_ = stack[4].m_obj;
lean_object* v___y_821_ = stack[5].m_obj;
lean_object* v___y_822_ = stack[6].m_obj;
lean_object* v___y_823_ = stack[7].m_obj;
lean_object* v_res_893_;
v_res_893_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
stack->m_obj
 = v_res_893_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object* v_msg_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
return v_res_903_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2));
v___x_908_ = lean_unsigned_to_nat(53u);
v___x_909_ = lean_unsigned_to_nat(62u);
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1));
v___x_911_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0));
v___x_912_ = l_mkPanicMessageWithDecl(v___x_911_, v___x_910_, v___x_909_, v___x_908_, v___x_907_);
return v___x_912_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t v_sz_913_, size_t v_i_914_, lean_object* v_bs_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
uint8_t v___x_924_; 
v___x_924_ = lean_usize_dec_lt(v_i_914_, v_sz_913_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; 
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v_bs_915_);
return v___x_925_;
}
else
{
lean_object* v_v_926_; lean_object* v___x_927_; lean_object* v_bs_x27_928_; lean_object* v_a_930_; lean_object* v___x_935_; 
v_v_926_ = lean_array_uget(v_bs_915_, v_i_914_);
v___x_927_ = lean_unsigned_to_nat(0u);
v_bs_x27_928_ = lean_array_uset(v_bs_915_, v_i_914_, v___x_927_);
v___x_935_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_v_926_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_935_) == 0)
{
lean_object* v_a_936_; 
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec_ref_known(v___x_935_, 1);
if (lean_obj_tag(v_a_936_) == 6)
{
lean_object* v_val_937_; lean_object* v_numFields_938_; uint8_t v___x_939_; lean_object* v___x_940_; 
v_val_937_ = lean_ctor_get(v_a_936_, 0);
lean_inc_ref(v_val_937_);
lean_dec_ref_known(v_a_936_, 1);
v_numFields_938_ = lean_ctor_get(v_val_937_, 4);
lean_inc(v_numFields_938_);
lean_dec_ref(v_val_937_);
v___x_939_ = 0;
v___x_940_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_940_, 0, v_numFields_938_);
lean_ctor_set(v___x_940_, 1, v___x_927_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*2, v___x_939_);
v_a_930_ = v___x_940_;
goto v___jp_929_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; 
lean_dec(v_a_936_);
v___x_941_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3);
v___x_942_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v___x_941_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v_a_930_ = v_a_943_;
goto v___jp_929_;
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec_ref(v_bs_x27_928_);
v_a_944_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_942_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_942_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec_ref(v_bs_x27_928_);
v_a_952_ = lean_ctor_get(v___x_935_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_935_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_935_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
v___jp_929_:
{
size_t v___x_931_; size_t v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((size_t)1ULL);
v___x_932_ = lean_usize_add(v_i_914_, v___x_931_);
v___x_933_ = lean_array_uset(v_bs_x27_928_, v_i_914_, v_a_930_);
v_i_914_ = v___x_932_;
v_bs_915_ = v___x_933_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_913_ = stack[0].m_num;
size_t v_i_914_ = stack[1].m_num;
lean_object* v_bs_915_ = stack[2].m_obj;
lean_object* v___y_916_ = stack[3].m_obj;
lean_object* v___y_917_ = stack[4].m_obj;
lean_object* v___y_918_ = stack[5].m_obj;
lean_object* v___y_919_ = stack[6].m_obj;
lean_object* v___y_920_ = stack[7].m_obj;
lean_object* v___y_921_ = stack[8].m_obj;
lean_object* v___y_922_ = stack[9].m_obj;
lean_object* v_res_960_;
v_res_960_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_913_, v_i_914_, v_bs_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object* v_sz_961_, lean_object* v_i_962_, lean_object* v_bs_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
size_t v_sz_boxed_972_; size_t v_i_boxed_973_; lean_object* v_res_974_; 
v_sz_boxed_972_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v_i_boxed_973_ = lean_unbox_usize(v_i_962_);
lean_dec(v_i_962_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_boxed_972_, v_i_boxed_973_, v_bs_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
return v_res_974_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object* v_declName_975_, lean_object* v___y_976_){
_start:
{
lean_object* v___x_978_; lean_object* v_env_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = lean_st_ref_get(v___y_976_);
v_env_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc_ref(v_env_979_);
lean_dec(v___x_978_);
v___x_980_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_979_, v_declName_975_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_975_ = stack[0].m_obj;
lean_object* v___y_976_ = stack[1].m_obj;
lean_object* v_res_982_;
v_res_982_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_975_, v___y_976_);
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object* v_declName_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_983_, v___y_984_);
lean_dec(v___y_984_);
return v_res_986_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_987_; lean_object* v_dummy_988_; 
v___x_987_ = lean_box(0);
v_dummy_988_ = l_Lean_Expr_sort___override(v___x_987_);
return v_dummy_988_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_989_ = lean_box(0);
v___x_990_ = lean_unsigned_to_nat(16u);
v___x_991_ = lean_mk_array(v___x_990_, v___x_989_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_992_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_992_);
return v___x_994_;
}
}
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object* v_e_997_, uint8_t v_alsoCasesOn_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
uint8_t v___x_1010_; 
v___x_1010_ = l_Lean_Expr_isApp(v_e_997_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
lean_dec_ref(v_e_997_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
return v___x_1012_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Expr_getAppFn(v_e_997_);
if (lean_obj_tag(v___x_1013_) == 4)
{
lean_object* v_declName_1014_; lean_object* v_us_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1170_; 
v_declName_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_n(v_declName_1014_, 2);
v_us_1015_ = lean_ctor_get(v___x_1013_, 1);
lean_inc(v_us_1015_);
lean_dec_ref_known(v___x_1013_, 2);
v___x_1016_ = l_Lean_instInhabitedExpr;
v___x_1017_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1014_, v___y_1005_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1170_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1170_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
if (lean_obj_tag(v_a_1018_) == 1)
{
lean_object* v_val_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1063_; 
v_val_1022_ = lean_ctor_get(v_a_1018_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_a_1018_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1024_ = v_a_1018_;
v_isShared_1025_ = v_isSharedCheck_1063_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_val_1022_);
lean_dec(v_a_1018_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1063_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v_dummy_1026_; lean_object* v_nargs_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v_args_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_dummy_1026_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_1027_ = l_Lean_Expr_getAppNumArgs(v_e_997_);
lean_inc(v_nargs_1027_);
v___x_1028_ = lean_mk_array(v_nargs_1027_, v_dummy_1026_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_sub(v_nargs_1027_, v___x_1029_);
lean_dec(v_nargs_1027_);
v_args_1031_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_997_, v___x_1028_, v___x_1030_);
v___x_1032_ = lean_array_get_size(v_args_1031_);
v___x_1033_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1022_);
v___x_1034_ = lean_nat_dec_lt(v___x_1032_, v___x_1033_);
lean_dec(v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v_numParams_1035_; lean_object* v_numDiscrs_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v_numParams_1035_ = lean_ctor_get(v_val_1022_, 0);
v_numDiscrs_1036_ = lean_ctor_get(v_val_1022_, 1);
v___x_1037_ = lean_array_mk(v_us_1015_);
v___x_1038_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1035_);
v___x_1039_ = l_Array_extract___redArg(v_args_1031_, v___x_1038_, v_numParams_1035_);
v___x_1040_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1022_);
v___x_1041_ = lean_array_get(v___x_1016_, v_args_1031_, v___x_1040_);
lean_dec(v___x_1040_);
v___x_1042_ = lean_nat_add(v_numParams_1035_, v___x_1029_);
v___x_1043_ = lean_nat_add(v___x_1042_, v_numDiscrs_1036_);
lean_inc(v___x_1043_);
lean_inc_ref_n(v_args_1031_, 2);
v___x_1044_ = l_Array_toSubarray___redArg(v_args_1031_, v___x_1042_, v___x_1043_);
v___x_1045_ = l_Subarray_copy___redArg(v___x_1044_);
v___x_1046_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1022_);
v___x_1047_ = lean_nat_add(v___x_1043_, v___x_1046_);
lean_dec(v___x_1046_);
lean_inc(v___x_1047_);
v___x_1048_ = l_Array_toSubarray___redArg(v_args_1031_, v___x_1043_, v___x_1047_);
v___x_1049_ = l_Subarray_copy___redArg(v___x_1048_);
v___x_1050_ = l_Array_toSubarray___redArg(v_args_1031_, v___x_1047_, v___x_1032_);
v___x_1051_ = l_Subarray_copy___redArg(v___x_1050_);
v___x_1052_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1052_, 0, v_val_1022_);
lean_ctor_set(v___x_1052_, 1, v_declName_1014_);
lean_ctor_set(v___x_1052_, 2, v___x_1037_);
lean_ctor_set(v___x_1052_, 3, v___x_1039_);
lean_ctor_set(v___x_1052_, 4, v___x_1041_);
lean_ctor_set(v___x_1052_, 5, v___x_1045_);
lean_ctor_set(v___x_1052_, 6, v___x_1049_);
lean_ctor_set(v___x_1052_, 7, v___x_1051_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1052_);
v___x_1054_ = v___x_1024_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1054_);
v___x_1056_ = v___x_1020_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
else
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
lean_dec_ref(v_args_1031_);
lean_del_object(v___x_1024_);
lean_dec(v_val_1022_);
lean_dec(v_us_1015_);
lean_dec(v_declName_1014_);
v___x_1059_ = lean_box(0);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 0, v___x_1059_);
v___x_1061_ = v___x_1020_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
else
{
lean_object* v___x_1064_; 
lean_del_object(v___x_1020_);
lean_dec(v_a_1018_);
v___x_1064_ = lean_st_ref_get(v___y_1005_);
if (v_alsoCasesOn_998_ == 0)
{
lean_dec(v___x_1064_);
lean_dec(v_us_1015_);
lean_dec(v_declName_1014_);
lean_dec_ref(v_e_997_);
goto v___jp_1007_;
}
else
{
lean_object* v_env_1065_; uint8_t v___x_1066_; 
v_env_1065_ = lean_ctor_get(v___x_1064_, 0);
lean_inc_ref(v_env_1065_);
lean_dec(v___x_1064_);
lean_inc(v_declName_1014_);
v___x_1066_ = l_Lean_isCasesOnRecursor(v_env_1065_, v_declName_1014_);
if (v___x_1066_ == 0)
{
lean_dec(v_us_1015_);
lean_dec(v_declName_1014_);
lean_dec_ref(v_e_997_);
goto v___jp_1007_;
}
else
{
lean_object* v_indName_1067_; lean_object* v___x_1068_; 
v_indName_1067_ = l_Lean_Name_getPrefix(v_declName_1014_);
v___x_1068_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_indName_1067_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1161_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1161_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1161_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
if (lean_obj_tag(v_a_1069_) == 5)
{
lean_object* v_val_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1156_; 
v_val_1073_ = lean_ctor_get(v_a_1069_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_a_1069_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1075_ = v_a_1069_;
v_isShared_1076_ = v_isSharedCheck_1156_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_val_1073_);
lean_dec(v_a_1069_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1156_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_toConstantVal_1077_; lean_object* v_numParams_1078_; lean_object* v_numIndices_1079_; lean_object* v_ctors_1080_; lean_object* v_nargs_1081_; lean_object* v_dummy_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v_args_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_toConstantVal_1077_ = lean_ctor_get(v_val_1073_, 0);
lean_inc_ref(v_toConstantVal_1077_);
v_numParams_1078_ = lean_ctor_get(v_val_1073_, 1);
lean_inc(v_numParams_1078_);
v_numIndices_1079_ = lean_ctor_get(v_val_1073_, 2);
lean_inc(v_numIndices_1079_);
v_ctors_1080_ = lean_ctor_get(v_val_1073_, 4);
lean_inc(v_ctors_1080_);
v_nargs_1081_ = l_Lean_Expr_getAppNumArgs(v_e_997_);
v_dummy_1082_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
lean_inc(v_nargs_1081_);
v___x_1083_ = lean_mk_array(v_nargs_1081_, v_dummy_1082_);
v___x_1084_ = lean_unsigned_to_nat(1u);
v___x_1085_ = lean_nat_sub(v_nargs_1081_, v___x_1084_);
lean_dec(v_nargs_1081_);
v_args_1086_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_997_, v___x_1083_, v___x_1085_);
v___x_1087_ = lean_nat_add(v_numParams_1078_, v___x_1084_);
v___x_1088_ = lean_nat_add(v___x_1087_, v_numIndices_1079_);
v___x_1089_ = lean_nat_add(v___x_1088_, v___x_1084_);
lean_dec(v___x_1088_);
v___x_1090_ = l_Lean_InductiveVal_numCtors(v_val_1073_);
lean_dec_ref(v_val_1073_);
v___x_1091_ = lean_nat_add(v___x_1089_, v___x_1090_);
lean_dec(v___x_1090_);
v___x_1092_ = lean_array_get_size(v_args_1086_);
v___x_1093_ = lean_nat_dec_le(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
lean_dec(v___x_1091_);
lean_dec(v___x_1089_);
lean_dec(v___x_1087_);
lean_dec_ref(v_args_1086_);
lean_dec(v_ctors_1080_);
lean_dec(v_numIndices_1079_);
lean_dec(v_numParams_1078_);
lean_dec_ref(v_toConstantVal_1077_);
lean_del_object(v___x_1075_);
lean_dec(v_us_1015_);
lean_dec(v_declName_1014_);
v___x_1094_ = lean_box(0);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1094_);
v___x_1096_ = v___x_1071_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
else
{
lean_object* v___x_1098_; lean_object* v_params_1099_; lean_object* v_motive_1100_; lean_object* v_discrs_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_discrInfos_1104_; lean_object* v_alts_1105_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v_lower_1147_; lean_object* v_upper_1148_; uint8_t v___x_1155_; 
lean_del_object(v___x_1071_);
v___x_1098_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1078_);
lean_inc_ref_n(v_args_1086_, 3);
v_params_1099_ = l_Array_toSubarray___redArg(v_args_1086_, v___x_1098_, v_numParams_1078_);
v_motive_1100_ = lean_array_get(v___x_1016_, v_args_1086_, v_numParams_1078_);
lean_dec(v_numParams_1078_);
lean_inc(v___x_1089_);
v_discrs_1101_ = l_Array_toSubarray___redArg(v_args_1086_, v___x_1087_, v___x_1089_);
v___x_1102_ = lean_nat_add(v_numIndices_1079_, v___x_1084_);
lean_dec(v_numIndices_1079_);
v___x_1103_ = lean_box(0);
v_discrInfos_1104_ = lean_mk_array(v___x_1102_, v___x_1103_);
lean_inc(v___x_1091_);
v_alts_1105_ = l_Array_toSubarray___redArg(v_args_1086_, v___x_1089_, v___x_1091_);
v___x_1155_ = lean_nat_dec_le(v___x_1091_, v___x_1098_);
if (v___x_1155_ == 0)
{
v_lower_1147_ = v___x_1091_;
v_upper_1148_ = v___x_1092_;
goto v___jp_1146_;
}
else
{
lean_dec(v___x_1091_);
v_lower_1147_ = v___x_1098_;
v_upper_1148_ = v___x_1092_;
goto v___jp_1146_;
}
v___jp_1106_:
{
lean_object* v___x_1109_; size_t v_sz_1110_; size_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1109_ = lean_array_mk(v_ctors_1080_);
v_sz_1110_ = lean_array_size(v___x_1109_);
v___x_1111_ = ((size_t)0ULL);
v___x_1112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_1110_, v___x_1111_, v___x_1109_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1137_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1137_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1137_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v_start_1117_; lean_object* v_stop_1118_; lean_object* v_start_1119_; lean_object* v_stop_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v_start_1117_ = lean_ctor_get(v_params_1099_, 1);
v_stop_1118_ = lean_ctor_get(v_params_1099_, 2);
v_start_1119_ = lean_ctor_get(v_discrs_1101_, 1);
v_stop_1120_ = lean_ctor_get(v_discrs_1101_, 2);
v___x_1121_ = lean_nat_sub(v_stop_1118_, v_start_1117_);
v___x_1122_ = lean_nat_sub(v_stop_1120_, v_start_1119_);
v___x_1123_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2);
v___x_1124_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1121_);
lean_ctor_set(v___x_1124_, 1, v___x_1122_);
lean_ctor_set(v___x_1124_, 2, v_a_1113_);
lean_ctor_set(v___x_1124_, 3, v___y_1108_);
lean_ctor_set(v___x_1124_, 4, v_discrInfos_1104_);
lean_ctor_set(v___x_1124_, 5, v___x_1123_);
v___x_1125_ = lean_array_mk(v_us_1015_);
v___x_1126_ = l_Subarray_copy___redArg(v_params_1099_);
v___x_1127_ = l_Subarray_copy___redArg(v_discrs_1101_);
v___x_1128_ = l_Subarray_copy___redArg(v_alts_1105_);
v___x_1129_ = l_Subarray_copy___redArg(v___y_1107_);
v___x_1130_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1124_);
lean_ctor_set(v___x_1130_, 1, v_declName_1014_);
lean_ctor_set(v___x_1130_, 2, v___x_1125_);
lean_ctor_set(v___x_1130_, 3, v___x_1126_);
lean_ctor_set(v___x_1130_, 4, v_motive_1100_);
lean_ctor_set(v___x_1130_, 5, v___x_1127_);
lean_ctor_set(v___x_1130_, 6, v___x_1128_);
lean_ctor_set(v___x_1130_, 7, v___x_1129_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set_tag(v___x_1075_, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1130_);
v___x_1132_ = v___x_1075_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
lean_object* v___x_1134_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1132_);
v___x_1134_ = v___x_1115_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1145_; 
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec_ref(v_alts_1105_);
lean_dec_ref(v_discrInfos_1104_);
lean_dec_ref(v_discrs_1101_);
lean_dec(v_motive_1100_);
lean_dec_ref(v_params_1099_);
lean_del_object(v___x_1075_);
lean_dec(v_us_1015_);
lean_dec(v_declName_1014_);
v_a_1138_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1140_ = v___x_1112_;
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_a_1138_);
lean_dec(v___x_1112_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1145_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1143_; 
if (v_isShared_1141_ == 0)
{
v___x_1143_ = v___x_1140_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1138_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
v___jp_1146_:
{
lean_object* v_levelParams_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_levelParams_1149_ = lean_ctor_get(v_toConstantVal_1077_, 1);
lean_inc(v_levelParams_1149_);
lean_dec_ref(v_toConstantVal_1077_);
v___x_1150_ = l_Array_toSubarray___redArg(v_args_1086_, v_lower_1147_, v_upper_1148_);
v___x_1151_ = l_List_lengthTR___redArg(v_levelParams_1149_);
lean_dec(v_levelParams_1149_);
v___x_1152_ = l_List_lengthTR___redArg(v_us_1015_);
v___x_1153_ = lean_nat_dec_eq(v___x_1151_, v___x_1152_);
lean_dec(v___x_1152_);
lean_dec(v___x_1151_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1154_; 
v___x_1154_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3));
v___y_1107_ = v___x_1150_;
v___y_1108_ = v___x_1154_;
goto v___jp_1106_;
}
else
{
v___y_1107_ = v___x_1150_;
v___y_1108_ = v___x_1103_;
goto v___jp_1106_;
}
}
}
}
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
lean_dec(v_a_1069_);
lean_dec(v_us_1015_);
lean_dec(v_declName_1014_);
lean_dec_ref(v_e_997_);
v___x_1157_ = lean_box(0);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1157_);
v___x_1159_ = v___x_1071_;
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
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1169_; 
lean_dec(v_us_1015_);
lean_dec(v_declName_1014_);
lean_dec_ref(v_e_997_);
v_a_1162_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1164_ = v___x_1068_;
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_a_1162_);
lean_dec(v___x_1068_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1169_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v___x_1167_; 
if (v_isShared_1165_ == 0)
{
v___x_1167_ = v___x_1164_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
v___x_1167_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
return v___x_1167_;
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
lean_dec_ref(v___x_1013_);
lean_dec_ref(v_e_997_);
goto v___jp_1007_;
}
}
v___jp_1007_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_997_ = stack[0].m_obj;
uint8_t v_alsoCasesOn_998_ = stack[1].m_num;
lean_object* v___y_999_ = stack[2].m_obj;
lean_object* v___y_1000_ = stack[3].m_obj;
lean_object* v___y_1001_ = stack[4].m_obj;
lean_object* v___y_1002_ = stack[5].m_obj;
lean_object* v___y_1003_ = stack[6].m_obj;
lean_object* v___y_1004_ = stack[7].m_obj;
lean_object* v___y_1005_ = stack[8].m_obj;
lean_object* v_res_1171_;
v_res_1171_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_997_, v_alsoCasesOn_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
stack->m_obj
 = v_res_1171_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object* v_e_1172_, lean_object* v_alsoCasesOn_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1182_; lean_object* v_res_1183_; 
v_alsoCasesOn_boxed_1182_ = lean_unbox(v_alsoCasesOn_1173_);
v_res_1183_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1172_, v_alsoCasesOn_boxed_1182_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
return v_res_1183_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t v_sz_1184_, size_t v_i_1185_, lean_object* v_bs_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
uint8_t v___x_1192_; 
v___x_1192_ = lean_usize_dec_lt(v_i_1185_, v_sz_1184_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_bs_1186_);
return v___x_1193_;
}
else
{
lean_object* v_v_1194_; lean_object* v___x_1195_; lean_object* v_bs_x27_1196_; lean_object* v___x_1197_; 
v_v_1194_ = lean_array_uget(v_bs_1186_, v_i_1185_);
v___x_1195_ = lean_unsigned_to_nat(0u);
v_bs_x27_1196_ = lean_array_uset(v_bs_1186_, v_i_1185_, v___x_1195_);
v___x_1197_ = l_Lean_Elab_WF_mkWfParam(v_v_1194_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; size_t v___x_1199_; size_t v___x_1200_; lean_object* v___x_1201_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v___x_1199_ = ((size_t)1ULL);
v___x_1200_ = lean_usize_add(v_i_1185_, v___x_1199_);
v___x_1201_ = lean_array_uset(v_bs_x27_1196_, v_i_1185_, v_a_1198_);
v_i_1185_ = v___x_1200_;
v_bs_1186_ = v___x_1201_;
goto _start;
}
else
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_bs_x27_1196_);
v_a_1203_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1197_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1197_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1184_ = stack[0].m_num;
size_t v_i_1185_ = stack[1].m_num;
lean_object* v_bs_1186_ = stack[2].m_obj;
lean_object* v___y_1187_ = stack[3].m_obj;
lean_object* v___y_1188_ = stack[4].m_obj;
lean_object* v___y_1189_ = stack[5].m_obj;
lean_object* v___y_1190_ = stack[6].m_obj;
lean_object* v_res_1211_;
v_res_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1184_, v_i_1185_, v_bs_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
stack->m_obj
 = v_res_1211_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object* v_sz_1212_, lean_object* v_i_1213_, lean_object* v_bs_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
size_t v_sz_boxed_1220_; size_t v_i_boxed_1221_; lean_object* v_res_1222_; 
v_sz_boxed_1220_ = lean_unbox_usize(v_sz_1212_);
lean_dec(v_sz_1212_);
v_i_boxed_1221_ = lean_unbox_usize(v_i_1213_);
lean_dec(v_i_1213_);
v_res_1222_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_boxed_1220_, v_i_boxed_1221_, v_bs_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
return v_res_1222_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(uint8_t v___x_1223_, lean_object* v_xs_1224_, lean_object* v_body_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
size_t v_sz_1234_; size_t v___x_1235_; lean_object* v___x_1236_; 
v_sz_1234_ = lean_array_size(v_xs_1224_);
v___x_1235_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1224_);
v___x_1236_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1234_, v___x_1235_, v_xs_1224_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1238_; uint8_t v___x_1239_; uint8_t v___x_1240_; lean_object* v___x_1241_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = l_Lean_Expr_replaceFVars(v_body_1225_, v_xs_1224_, v_a_1237_);
lean_dec(v_a_1237_);
v___x_1239_ = 0;
v___x_1240_ = 1;
v___x_1241_ = l_Lean_Meta_mkLambdaFVars(v_xs_1224_, v___x_1238_, v___x_1239_, v___x_1223_, v___x_1239_, v___x_1223_, v___x_1240_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec_ref(v_xs_1224_);
return v___x_1241_;
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec_ref(v_xs_1224_);
v_a_1242_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1236_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1236_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1223_ = stack[0].m_num;
lean_object* v_xs_1224_ = stack[1].m_obj;
lean_object* v_body_1225_ = stack[2].m_obj;
lean_object* v___y_1226_ = stack[3].m_obj;
lean_object* v___y_1227_ = stack[4].m_obj;
lean_object* v___y_1228_ = stack[5].m_obj;
lean_object* v___y_1229_ = stack[6].m_obj;
lean_object* v___y_1230_ = stack[7].m_obj;
lean_object* v___y_1231_ = stack[8].m_obj;
lean_object* v___y_1232_ = stack[9].m_obj;
lean_object* v_res_1250_;
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(v___x_1223_, v_xs_1224_, v_body_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
stack->m_obj
 = v_res_1250_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0___boxed(lean_object* v___x_1251_, lean_object* v_xs_1252_, lean_object* v_body_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v___x_23108__boxed_1262_; lean_object* v_res_1263_; 
v___x_23108__boxed_1262_ = lean_unbox(v___x_1251_);
v_res_1263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(v___x_23108__boxed_1262_, v_xs_1252_, v_body_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v_body_1253_);
return v_res_1263_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t v_sz_1264_, size_t v_i_1265_, lean_object* v_bs_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_usize_dec_lt(v_i_1265_, v_sz_1264_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1276_, 0, v_bs_1266_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___f_1278_; lean_object* v_v_1279_; lean_object* v___x_1280_; lean_object* v_bs_x27_1281_; uint8_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1277_ = lean_box(v___x_1275_);
v___f_1278_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1278_, 0, v___x_1277_);
v_v_1279_ = lean_array_uget(v_bs_1266_, v_i_1265_);
v___x_1280_ = lean_unsigned_to_nat(0u);
v_bs_x27_1281_ = lean_array_uset(v_bs_1266_, v_i_1265_, v___x_1280_);
v___x_1282_ = 0;
v___x_1283_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_v_1279_, v___f_1278_, v___x_1282_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_add(v_i_1265_, v___x_1285_);
v___x_1287_ = lean_array_uset(v_bs_x27_1281_, v_i_1265_, v_a_1284_);
v_i_1265_ = v___x_1286_;
v_bs_1266_ = v___x_1287_;
goto _start;
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
lean_dec_ref(v_bs_x27_1281_);
v_a_1289_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1283_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1283_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1264_ = stack[0].m_num;
size_t v_i_1265_ = stack[1].m_num;
lean_object* v_bs_1266_ = stack[2].m_obj;
lean_object* v___y_1267_ = stack[3].m_obj;
lean_object* v___y_1268_ = stack[4].m_obj;
lean_object* v___y_1269_ = stack[5].m_obj;
lean_object* v___y_1270_ = stack[6].m_obj;
lean_object* v___y_1271_ = stack[7].m_obj;
lean_object* v___y_1272_ = stack[8].m_obj;
lean_object* v___y_1273_ = stack[9].m_obj;
lean_object* v_res_1297_;
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1264_, v_i_1265_, v_bs_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
stack->m_obj
 = v_res_1297_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_bs_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
size_t v_sz_boxed_1309_; size_t v_i_boxed_1310_; lean_object* v_res_1311_; 
v_sz_boxed_1309_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1310_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_boxed_1309_, v_i_boxed_1310_, v_bs_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec_ref(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v___y_1302_);
lean_dec(v___y_1301_);
return v_res_1311_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object* v_as_1312_, size_t v_i_1313_, size_t v_stop_1314_){
_start:
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_usize_dec_eq(v_i_1313_, v_stop_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_array_uget_borrowed(v_as_1312_, v_i_1313_);
v___x_1317_ = l_Lean_Elab_WF_isWfParam_x3f(v___x_1316_);
if (lean_obj_tag(v___x_1317_) == 0)
{
size_t v___x_1318_; size_t v___x_1319_; 
v___x_1318_ = ((size_t)1ULL);
v___x_1319_ = lean_usize_add(v_i_1313_, v___x_1318_);
v_i_1313_ = v___x_1319_;
goto _start;
}
else
{
uint8_t v___x_1321_; 
lean_dec_ref_known(v___x_1317_, 1);
v___x_1321_ = 1;
return v___x_1321_;
}
}
else
{
uint8_t v___x_1322_; 
v___x_1322_ = 0;
return v___x_1322_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1312_ = stack[0].m_obj;
size_t v_i_1313_ = stack[1].m_num;
size_t v_stop_1314_ = stack[2].m_num;
uint8_t v_res_1323_;
v_res_1323_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1312_, v_i_1313_, v_stop_1314_);
stack->m_num = v_res_1323_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object* v_as_1324_, lean_object* v_i_1325_, lean_object* v_stop_1326_){
_start:
{
size_t v_i_boxed_1327_; size_t v_stop_boxed_1328_; uint8_t v_res_1329_; lean_object* v_r_1330_; 
v_i_boxed_1327_ = lean_unbox_usize(v_i_1325_);
lean_dec(v_i_1325_);
v_stop_boxed_1328_ = lean_unbox_usize(v_stop_1326_);
lean_dec(v_stop_1326_);
v_res_1329_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1324_, v_i_boxed_1327_, v_stop_boxed_1328_);
lean_dec_ref(v_as_1324_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
lean_object* l_Lean_Elab_WF_paramMatcher(lean_object* v_e_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
uint8_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1340_ = 1;
v___x_1341_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1331_, v___x_1340_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1404_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1344_ = v___x_1341_;
v_isShared_1345_ = v_isSharedCheck_1404_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1341_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1404_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
if (lean_obj_tag(v_a_1342_) == 1)
{
lean_object* v_val_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1401_; 
v_val_1351_ = lean_ctor_get(v_a_1342_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_a_1342_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1353_ = v_a_1342_;
v_isShared_1354_ = v_isSharedCheck_1401_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_val_1351_);
lean_dec(v_a_1342_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1401_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v_toMatcherInfo_1355_; lean_object* v_matcherName_1356_; lean_object* v_matcherLevels_1357_; lean_object* v_params_1358_; lean_object* v_motive_1359_; lean_object* v_discrs_1360_; lean_object* v_alts_1361_; lean_object* v_remaining_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1400_; 
v_toMatcherInfo_1355_ = lean_ctor_get(v_val_1351_, 0);
v_matcherName_1356_ = lean_ctor_get(v_val_1351_, 1);
v_matcherLevels_1357_ = lean_ctor_get(v_val_1351_, 2);
v_params_1358_ = lean_ctor_get(v_val_1351_, 3);
v_motive_1359_ = lean_ctor_get(v_val_1351_, 4);
v_discrs_1360_ = lean_ctor_get(v_val_1351_, 5);
v_alts_1361_ = lean_ctor_get(v_val_1351_, 6);
v_remaining_1362_ = lean_ctor_get(v_val_1351_, 7);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_val_1351_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1364_ = v_val_1351_;
v_isShared_1365_ = v_isSharedCheck_1400_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_remaining_1362_);
lean_inc(v_alts_1361_);
lean_inc(v_discrs_1360_);
lean_inc(v_motive_1359_);
lean_inc(v_params_1358_);
lean_inc(v_matcherLevels_1357_);
lean_inc(v_matcherName_1356_);
lean_inc(v_toMatcherInfo_1355_);
lean_dec(v_val_1351_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1400_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_array_get_size(v_discrs_1360_);
v___x_1368_ = lean_nat_dec_lt(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_del_object(v___x_1364_);
lean_dec_ref(v_remaining_1362_);
lean_dec_ref(v_alts_1361_);
lean_dec_ref(v_discrs_1360_);
lean_dec_ref(v_motive_1359_);
lean_dec_ref(v_params_1358_);
lean_dec_ref(v_matcherLevels_1357_);
lean_dec(v_matcherName_1356_);
lean_dec_ref(v_toMatcherInfo_1355_);
lean_del_object(v___x_1353_);
goto v___jp_1346_;
}
else
{
if (v___x_1368_ == 0)
{
lean_del_object(v___x_1364_);
lean_dec_ref(v_remaining_1362_);
lean_dec_ref(v_alts_1361_);
lean_dec_ref(v_discrs_1360_);
lean_dec_ref(v_motive_1359_);
lean_dec_ref(v_params_1358_);
lean_dec_ref(v_matcherLevels_1357_);
lean_dec(v_matcherName_1356_);
lean_dec_ref(v_toMatcherInfo_1355_);
lean_del_object(v___x_1353_);
goto v___jp_1346_;
}
else
{
size_t v___x_1369_; size_t v___x_1370_; uint8_t v___x_1371_; 
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1367_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_discrs_1360_, v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_del_object(v___x_1364_);
lean_dec_ref(v_remaining_1362_);
lean_dec_ref(v_alts_1361_);
lean_dec_ref(v_discrs_1360_);
lean_dec_ref(v_motive_1359_);
lean_dec_ref(v_params_1358_);
lean_dec_ref(v_matcherLevels_1357_);
lean_dec(v_matcherName_1356_);
lean_dec_ref(v_toMatcherInfo_1355_);
lean_del_object(v___x_1353_);
goto v___jp_1346_;
}
else
{
size_t v_sz_1372_; lean_object* v___x_1373_; size_t v_sz_1374_; lean_object* v___x_1375_; 
lean_del_object(v___x_1344_);
v_sz_1372_ = lean_array_size(v_discrs_1360_);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_1372_, v___x_1369_, v_discrs_1360_);
v_sz_1374_ = lean_array_size(v_alts_1361_);
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1374_, v___x_1369_, v_alts_1361_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1391_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1391_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1391_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 6, v_a_1376_);
lean_ctor_set(v___x_1364_, 5, v___x_1373_);
v___x_1381_ = v___x_1364_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_toMatcherInfo_1355_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_matcherName_1356_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_matcherLevels_1357_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_params_1358_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_motive_1359_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v_a_1376_);
lean_ctor_set(v_reuseFailAlloc_1390_, 7, v_remaining_1362_);
v___x_1381_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1382_ = l_Lean_Meta_MatcherApp_toExpr(v___x_1381_);
if (v_isShared_1354_ == 0)
{
lean_ctor_set(v___x_1353_, 0, v___x_1382_);
v___x_1384_ = v___x_1353_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 0, v___x_1385_);
v___x_1387_ = v___x_1378_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
}
else
{
lean_object* v_a_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1399_; 
lean_dec_ref(v___x_1373_);
lean_del_object(v___x_1364_);
lean_dec_ref(v_remaining_1362_);
lean_dec_ref(v_motive_1359_);
lean_dec_ref(v_params_1358_);
lean_dec_ref(v_matcherLevels_1357_);
lean_dec(v_matcherName_1356_);
lean_dec_ref(v_toMatcherInfo_1355_);
lean_del_object(v___x_1353_);
v_a_1392_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1394_ = v___x_1375_;
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_a_1392_);
lean_dec(v___x_1375_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1399_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_a_1392_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
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
lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_del_object(v___x_1344_);
lean_dec(v_a_1342_);
v___x_1402_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
return v___x_1403_;
}
v___jp_1346_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1347_);
v___x_1349_ = v___x_1344_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v___x_1347_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1341_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1341_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_paramMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1331_ = stack[0].m_obj;
lean_object* v_a_1332_ = stack[1].m_obj;
lean_object* v_a_1333_ = stack[2].m_obj;
lean_object* v_a_1334_ = stack[3].m_obj;
lean_object* v_a_1335_ = stack[4].m_obj;
lean_object* v_a_1336_ = stack[5].m_obj;
lean_object* v_a_1337_ = stack[6].m_obj;
lean_object* v_a_1338_ = stack[7].m_obj;
lean_object* v_res_1413_;
v_res_1413_ = l_Lean_Elab_WF_paramMatcher(v_e_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
stack->m_obj
 = v_res_1413_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object* v_e_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_Elab_WF_paramMatcher(v_e_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1421_);
lean_dec_ref(v_a_1420_);
lean_dec(v_a_1419_);
lean_dec_ref(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec_ref(v_a_1416_);
lean_dec(v_a_1415_);
return v_res_1423_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t v_sz_1424_, size_t v_i_1425_, lean_object* v_bs_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1424_, v_i_1425_, v_bs_1426_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1435_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1424_ = stack[0].m_num;
size_t v_i_1425_ = stack[1].m_num;
lean_object* v_bs_1426_ = stack[2].m_obj;
lean_object* v___y_1427_ = stack[3].m_obj;
lean_object* v___y_1428_ = stack[4].m_obj;
lean_object* v___y_1429_ = stack[5].m_obj;
lean_object* v___y_1430_ = stack[6].m_obj;
lean_object* v___y_1431_ = stack[7].m_obj;
lean_object* v___y_1432_ = stack[8].m_obj;
lean_object* v___y_1433_ = stack[9].m_obj;
lean_object* v_res_1436_;
v_res_1436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_1424_, v_i_1425_, v_bs_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
stack->m_obj
 = v_res_1436_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object* v_sz_1437_, lean_object* v_i_1438_, lean_object* v_bs_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
size_t v_sz_boxed_1448_; size_t v_i_boxed_1449_; lean_object* v_res_1450_; 
v_sz_boxed_1448_ = lean_unbox_usize(v_sz_1437_);
lean_dec(v_sz_1437_);
v_i_boxed_1449_ = lean_unbox_usize(v_i_1438_);
lean_dec(v_i_1438_);
v_res_1450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_boxed_1448_, v_i_boxed_1449_, v_bs_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
return v_res_1450_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object* v_declName_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1451_, v___y_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1451_ = stack[0].m_obj;
lean_object* v___y_1452_ = stack[1].m_obj;
lean_object* v___y_1453_ = stack[2].m_obj;
lean_object* v___y_1454_ = stack[3].m_obj;
lean_object* v___y_1455_ = stack[4].m_obj;
lean_object* v___y_1456_ = stack[5].m_obj;
lean_object* v___y_1457_ = stack[6].m_obj;
lean_object* v___y_1458_ = stack[7].m_obj;
lean_object* v_res_1461_;
v_res_1461_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
stack->m_obj
 = v_res_1461_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object* v_declName_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
return v_res_1471_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_1472_, lean_object* v_constName_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1473_ = stack[1].m_obj;
lean_object* v___y_1474_ = stack[2].m_obj;
lean_object* v___y_1475_ = stack[3].m_obj;
lean_object* v___y_1476_ = stack[4].m_obj;
lean_object* v___y_1477_ = stack[5].m_obj;
lean_object* v___y_1478_ = stack[6].m_obj;
lean_object* v___y_1479_ = stack[7].m_obj;
lean_object* v___y_1480_ = stack[8].m_obj;
lean_object* v_res_1483_;
v_res_1483_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_box(0), v_constName_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
stack->m_obj
 = v_res_1483_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1484_, lean_object* v_constName_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(v_00_u03b1_1484_, v_constName_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
return v_res_1494_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b1_1495_, lean_object* v_ref_1496_, lean_object* v_constName_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_1496_, v_constName_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1496_ = stack[1].m_obj;
lean_object* v_constName_1497_ = stack[2].m_obj;
lean_object* v___y_1498_ = stack[3].m_obj;
lean_object* v___y_1499_ = stack[4].m_obj;
lean_object* v___y_1500_ = stack[5].m_obj;
lean_object* v___y_1501_ = stack[6].m_obj;
lean_object* v___y_1502_ = stack[7].m_obj;
lean_object* v___y_1503_ = stack[8].m_obj;
lean_object* v___y_1504_ = stack[9].m_obj;
lean_object* v_res_1507_;
v_res_1507_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_box(0), v_ref_1496_, v_constName_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
stack->m_obj
 = v_res_1507_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b1_1508_, lean_object* v_ref_1509_, lean_object* v_constName_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(v_00_u03b1_1508_, v_ref_1509_, v_constName_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec(v_ref_1509_);
return v_res_1519_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_1520_, lean_object* v_ref_1521_, lean_object* v_msg_1522_, lean_object* v_declHint_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_1521_, v_msg_1522_, v_declHint_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1521_ = stack[1].m_obj;
lean_object* v_msg_1522_ = stack[2].m_obj;
lean_object* v_declHint_1523_ = stack[3].m_obj;
lean_object* v___y_1524_ = stack[4].m_obj;
lean_object* v___y_1525_ = stack[5].m_obj;
lean_object* v___y_1526_ = stack[6].m_obj;
lean_object* v___y_1527_ = stack[7].m_obj;
lean_object* v___y_1528_ = stack[8].m_obj;
lean_object* v___y_1529_ = stack[9].m_obj;
lean_object* v___y_1530_ = stack[10].m_obj;
lean_object* v_res_1533_;
v_res_1533_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_box(0), v_ref_1521_, v_msg_1522_, v_declHint_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
stack->m_obj
 = v_res_1533_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1534_, lean_object* v_ref_1535_, lean_object* v_msg_1536_, lean_object* v_declHint_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_1534_, v_ref_1535_, v_msg_1536_, v_declHint_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec(v_ref_1535_);
return v_res_1546_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1547_, lean_object* v_declHint_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1547_, v_declHint_1548_, v___y_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1547_ = stack[0].m_obj;
lean_object* v_declHint_1548_ = stack[1].m_obj;
lean_object* v___y_1549_ = stack[2].m_obj;
lean_object* v___y_1550_ = stack[3].m_obj;
lean_object* v___y_1551_ = stack[4].m_obj;
lean_object* v___y_1552_ = stack[5].m_obj;
lean_object* v___y_1553_ = stack[6].m_obj;
lean_object* v___y_1554_ = stack[7].m_obj;
lean_object* v___y_1555_ = stack[8].m_obj;
lean_object* v_res_1558_;
v_res_1558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1547_, v_declHint_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1559_, lean_object* v_declHint_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1559_, v_declHint_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
return v_res_1569_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1570_, lean_object* v_ref_1571_, lean_object* v_msg_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_1571_, v_msg_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
return v___x_1581_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1571_ = stack[1].m_obj;
lean_object* v_msg_1572_ = stack[2].m_obj;
lean_object* v___y_1573_ = stack[3].m_obj;
lean_object* v___y_1574_ = stack[4].m_obj;
lean_object* v___y_1575_ = stack[5].m_obj;
lean_object* v___y_1576_ = stack[6].m_obj;
lean_object* v___y_1577_ = stack[7].m_obj;
lean_object* v___y_1578_ = stack[8].m_obj;
lean_object* v___y_1579_ = stack[9].m_obj;
lean_object* v_res_1582_;
v_res_1582_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_box(0), v_ref_1571_, v_msg_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
stack->m_obj
 = v_res_1582_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1583_, lean_object* v_ref_1584_, lean_object* v_msg_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(v_00_u03b1_1583_, v_ref_1584_, v_msg_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec(v_ref_1584_);
return v_res_1594_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_1595_, lean_object* v_msg_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_1596_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
return v___x_1605_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1596_ = stack[1].m_obj;
lean_object* v___y_1597_ = stack[2].m_obj;
lean_object* v___y_1598_ = stack[3].m_obj;
lean_object* v___y_1599_ = stack[4].m_obj;
lean_object* v___y_1600_ = stack[5].m_obj;
lean_object* v___y_1601_ = stack[6].m_obj;
lean_object* v___y_1602_ = stack[7].m_obj;
lean_object* v___y_1603_ = stack[8].m_obj;
lean_object* v_res_1606_;
v_res_1606_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_box(0), v_msg_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
stack->m_obj
 = v_res_1606_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1607_, lean_object* v_msg_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(v_00_u03b1_1607_, v_msg_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
return v_res_1617_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_));
v___x_1626_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_1627_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1628_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1625_, v___x_1626_, v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1629_;
v_res_1629_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_();
stack->m_obj
 = v_res_1629_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10____boxed(lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_();
return v_res_1631_;
}
}
uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object* v_e_1632_){
_start:
{
if (lean_obj_tag(v_e_1632_) == 8)
{
lean_object* v_value_1633_; lean_object* v_body_1634_; lean_object* v___x_1635_; 
v_value_1633_ = lean_ctor_get(v_e_1632_, 2);
v_body_1634_ = lean_ctor_get(v_e_1632_, 3);
v___x_1635_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
v_e_1632_ = v_body_1634_;
goto _start;
}
else
{
uint8_t v___x_1637_; 
lean_dec_ref_known(v___x_1635_, 1);
v___x_1637_ = 1;
return v___x_1637_;
}
}
else
{
uint8_t v___x_1638_; 
v___x_1638_ = 0;
return v___x_1638_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1632_ = stack[0].m_obj;
uint8_t v_res_1639_;
v_res_1639_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1632_);
stack->m_num = v_res_1639_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object* v_e_1640_){
_start:
{
uint8_t v_res_1641_; lean_object* v_r_1642_; 
v_res_1641_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1640_);
lean_dec_ref(v_e_1640_);
v_r_1642_ = lean_box(v_res_1641_);
return v_r_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object* v_e_1643_, lean_object* v_acc_1644_){
_start:
{
if (lean_obj_tag(v_e_1643_) == 8)
{
lean_object* v_value_1645_; lean_object* v_body_1646_; lean_object* v___x_1647_; 
v_value_1645_ = lean_ctor_get(v_e_1643_, 2);
v_body_1646_ = lean_ctor_get(v_e_1643_, 3);
v___x_1647_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1645_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_nat_add(v_acc_1644_, v___x_1648_);
lean_dec(v_acc_1644_);
v_e_1643_ = v_body_1646_;
v_acc_1644_ = v___x_1649_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1647_, 1);
return v_acc_1644_;
}
}
else
{
return v_acc_1644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object* v_e_1651_, lean_object* v_acc_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1651_, v_acc_1652_);
lean_dec_ref(v_e_1651_);
return v_res_1653_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object* v_msg_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___f_1661_; lean_object* v___x_1085__overap_1662_; lean_object* v___x_1663_; 
v___f_1661_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0));
v___x_1085__overap_1662_ = lean_panic_fn_borrowed(v___f_1661_, v_msg_1655_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
v___x_1663_ = lean_apply_5(v___x_1085__overap_1662_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, lean_box(0));
return v___x_1663_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1655_ = stack[0].m_obj;
lean_object* v___y_1656_ = stack[1].m_obj;
lean_object* v___y_1657_ = stack[2].m_obj;
lean_object* v___y_1658_ = stack[3].m_obj;
lean_object* v___y_1659_ = stack[4].m_obj;
lean_object* v_res_1664_;
v_res_1664_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_);
stack->m_obj
 = v_res_1664_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
return v_res_1671_;
}
}
lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object* v_k_1672_, lean_object* v_b_1673_, lean_object* v_c_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v___x_1680_; 
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
v___x_1680_ = lean_apply_7(v_k_1672_, v_b_1673_, v_c_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, lean_box(0));
return v___x_1680_;
}
}
LEAN_EXPORT void l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1672_ = stack[0].m_obj;
lean_object* v_b_1673_ = stack[1].m_obj;
lean_object* v_c_1674_ = stack[2].m_obj;
lean_object* v___y_1675_ = stack[3].m_obj;
lean_object* v___y_1676_ = stack[4].m_obj;
lean_object* v___y_1677_ = stack[5].m_obj;
lean_object* v___y_1678_ = stack[6].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1672_, v_b_1673_, v_c_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
stack->m_obj
 = v_res_1681_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object* v_k_1682_, lean_object* v_b_1683_, lean_object* v_c_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1682_, v_b_1683_, v_c_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v_res_1690_;
}
}
lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object* v_e_1691_, lean_object* v_maxFVars_x3f_1692_, lean_object* v_k_1693_, uint8_t v_cleanupAnnotations_1694_, uint8_t v_preserveNondepLet_1695_, uint8_t v_nondepLetOnly_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___f_1702_; uint8_t v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; 
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1702_, 0, v_k_1693_);
v___x_1703_ = 0;
v___x_1704_ = 1;
v___x_1705_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1691_, v___x_1703_, v___x_1704_, v_preserveNondepLet_1695_, v_nondepLetOnly_1696_, v_maxFVars_x3f_1692_, v___f_1702_, v_cleanupAnnotations_1694_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1713_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1708_ = v___x_1705_;
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_a_1706_);
lean_dec(v___x_1705_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1713_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1711_; 
if (v_isShared_1709_ == 0)
{
v___x_1711_ = v___x_1708_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1706_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
v_a_1714_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1705_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1705_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1691_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_1692_ = stack[1].m_obj;
lean_object* v_k_1693_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_1694_ = stack[3].m_num;
uint8_t v_preserveNondepLet_1695_ = stack[4].m_num;
uint8_t v_nondepLetOnly_1696_ = stack[5].m_num;
lean_object* v___y_1697_ = stack[6].m_obj;
lean_object* v___y_1698_ = stack[7].m_obj;
lean_object* v___y_1699_ = stack[8].m_obj;
lean_object* v___y_1700_ = stack[9].m_obj;
lean_object* v_res_1722_;
v_res_1722_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1691_, v_maxFVars_x3f_1692_, v_k_1693_, v_cleanupAnnotations_1694_, v_preserveNondepLet_1695_, v_nondepLetOnly_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
stack->m_obj
 = v_res_1722_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object* v_e_1723_, lean_object* v_maxFVars_x3f_1724_, lean_object* v_k_1725_, lean_object* v_cleanupAnnotations_1726_, lean_object* v_preserveNondepLet_1727_, lean_object* v_nondepLetOnly_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1734_; uint8_t v_preserveNondepLet_boxed_1735_; uint8_t v_nondepLetOnly_boxed_1736_; lean_object* v_res_1737_; 
v_cleanupAnnotations_boxed_1734_ = lean_unbox(v_cleanupAnnotations_1726_);
v_preserveNondepLet_boxed_1735_ = lean_unbox(v_preserveNondepLet_1727_);
v_nondepLetOnly_boxed_1736_ = lean_unbox(v_nondepLetOnly_1728_);
v_res_1737_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1723_, v_maxFVars_x3f_1724_, v_k_1725_, v_cleanupAnnotations_boxed_1734_, v_preserveNondepLet_boxed_1735_, v_nondepLetOnly_boxed_1736_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v_maxFVars_x3f_1724_);
return v_res_1737_;
}
}
lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object* v_00_u03b1_1738_, lean_object* v_e_1739_, lean_object* v_maxFVars_x3f_1740_, lean_object* v_k_1741_, uint8_t v_cleanupAnnotations_1742_, uint8_t v_preserveNondepLet_1743_, uint8_t v_nondepLetOnly_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1739_, v_maxFVars_x3f_1740_, v_k_1741_, v_cleanupAnnotations_1742_, v_preserveNondepLet_1743_, v_nondepLetOnly_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
return v___x_1750_;
}
}
LEAN_EXPORT void l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1739_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_1740_ = stack[2].m_obj;
lean_object* v_k_1741_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_1742_ = stack[4].m_num;
uint8_t v_preserveNondepLet_1743_ = stack[5].m_num;
uint8_t v_nondepLetOnly_1744_ = stack[6].m_num;
lean_object* v___y_1745_ = stack[7].m_obj;
lean_object* v___y_1746_ = stack[8].m_obj;
lean_object* v___y_1747_ = stack[9].m_obj;
lean_object* v___y_1748_ = stack[10].m_obj;
lean_object* v_res_1751_;
v_res_1751_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_box(0), v_e_1739_, v_maxFVars_x3f_1740_, v_k_1741_, v_cleanupAnnotations_1742_, v_preserveNondepLet_1743_, v_nondepLetOnly_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
stack->m_obj
 = v_res_1751_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object* v_00_u03b1_1752_, lean_object* v_e_1753_, lean_object* v_maxFVars_x3f_1754_, lean_object* v_k_1755_, lean_object* v_cleanupAnnotations_1756_, lean_object* v_preserveNondepLet_1757_, lean_object* v_nondepLetOnly_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1764_; uint8_t v_preserveNondepLet_boxed_1765_; uint8_t v_nondepLetOnly_boxed_1766_; lean_object* v_res_1767_; 
v_cleanupAnnotations_boxed_1764_ = lean_unbox(v_cleanupAnnotations_1756_);
v_preserveNondepLet_boxed_1765_ = lean_unbox(v_preserveNondepLet_1757_);
v_nondepLetOnly_boxed_1766_ = lean_unbox(v_nondepLetOnly_1758_);
v_res_1767_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(v_00_u03b1_1752_, v_e_1753_, v_maxFVars_x3f_1754_, v_k_1755_, v_cleanupAnnotations_boxed_1764_, v_preserveNondepLet_boxed_1765_, v_nondepLetOnly_boxed_1766_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v_maxFVars_x3f_1754_);
return v_res_1767_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_unsigned_to_nat(0u);
v___x_1769_ = l_Lean_Expr_bvar___override(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1773_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3));
v___x_1774_ = lean_unsigned_to_nat(6u);
v___x_1775_ = lean_unsigned_to_nat(142u);
v___x_1776_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2));
v___x_1777_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1));
v___x_1778_ = l_mkPanicMessageWithDecl(v___x_1777_, v___x_1776_, v___x_1775_, v___x_1774_, v___x_1773_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object* v_xs_1779_, lean_object* v_b_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1779_, v_b_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v_xs_1779_);
return v_res_1786_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object* v_e_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
if (lean_obj_tag(v_e_1787_) == 8)
{
lean_object* v_declName_1793_; lean_object* v_type_1794_; lean_object* v_value_1795_; lean_object* v_body_1796_; uint8_t v_nondep_1797_; lean_object* v___x_1798_; 
v_declName_1793_ = lean_ctor_get(v_e_1787_, 0);
v_type_1794_ = lean_ctor_get(v_e_1787_, 1);
v_value_1795_ = lean_ctor_get(v_e_1787_, 2);
v_body_1796_ = lean_ctor_get(v_e_1787_, 3);
v_nondep_1797_ = lean_ctor_get_uint8(v_e_1787_, sizeof(void*)*4 + 8);
v___x_1798_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1795_);
if (lean_obj_tag(v___x_1798_) == 1)
{
lean_object* v_val_1799_; lean_object* v___x_1800_; 
v_val_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_val_1799_);
lean_dec_ref_known(v___x_1798_, 1);
lean_inc_ref(v_type_1794_);
v___x_1800_ = l_Lean_Meta_isProp(v_type_1794_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; uint8_t v___x_1802_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = lean_unbox(v_a_1801_);
lean_dec(v_a_1801_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; 
lean_inc_ref(v_type_1794_);
v___x_1803_ = l_Lean_Meta_getLevel(v_type_1794_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; size_t v___x_1812_; uint8_t v___x_1813_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1804_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = l_Lean_Expr_const___override(v___x_1805_, v___x_1807_);
v___x_1809_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0);
lean_inc_ref(v_type_1794_);
v___x_1810_ = l_Lean_mkAppB(v___x_1808_, v_type_1794_, v___x_1809_);
v___x_1811_ = lean_expr_instantiate1(v_body_1796_, v___x_1810_);
lean_dec_ref(v___x_1810_);
v___x_1812_ = lean_ptr_addr(v_type_1794_);
v___x_1813_ = lean_usize_dec_eq(v___x_1812_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
lean_inc_ref(v_type_1794_);
lean_inc(v_declName_1793_);
lean_dec_ref_known(v_e_1787_, 4);
v___x_1814_ = l_Lean_Expr_letE___override(v_declName_1793_, v_type_1794_, v_val_1799_, v___x_1811_, v_nondep_1797_);
v_e_1787_ = v___x_1814_;
goto _start;
}
else
{
size_t v___x_1816_; size_t v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_ptr_addr(v_value_1795_);
v___x_1817_ = lean_ptr_addr(v_val_1799_);
v___x_1818_ = lean_usize_dec_eq(v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1819_; 
lean_inc_ref(v_type_1794_);
lean_inc(v_declName_1793_);
lean_dec_ref_known(v_e_1787_, 4);
v___x_1819_ = l_Lean_Expr_letE___override(v_declName_1793_, v_type_1794_, v_val_1799_, v___x_1811_, v_nondep_1797_);
v_e_1787_ = v___x_1819_;
goto _start;
}
else
{
size_t v___x_1821_; size_t v___x_1822_; uint8_t v___x_1823_; 
v___x_1821_ = lean_ptr_addr(v_body_1796_);
v___x_1822_ = lean_ptr_addr(v___x_1811_);
v___x_1823_ = lean_usize_dec_eq(v___x_1821_, v___x_1822_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_inc_ref(v_type_1794_);
lean_inc(v_declName_1793_);
lean_dec_ref_known(v_e_1787_, 4);
v___x_1824_ = l_Lean_Expr_letE___override(v_declName_1793_, v_type_1794_, v_val_1799_, v___x_1811_, v_nondep_1797_);
v_e_1787_ = v___x_1824_;
goto _start;
}
else
{
lean_dec_ref(v___x_1811_);
lean_dec(v_val_1799_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
lean_dec(v_val_1799_);
lean_dec_ref_known(v_e_1787_, 4);
v_a_1827_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1803_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1803_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
else
{
size_t v___x_1835_; uint8_t v___x_1836_; 
v___x_1835_ = lean_ptr_addr(v_type_1794_);
v___x_1836_ = lean_usize_dec_eq(v___x_1835_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; 
lean_inc_ref(v_body_1796_);
lean_inc_ref(v_type_1794_);
lean_inc(v_declName_1793_);
lean_dec_ref_known(v_e_1787_, 4);
v___x_1837_ = l_Lean_Expr_letE___override(v_declName_1793_, v_type_1794_, v_val_1799_, v_body_1796_, v_nondep_1797_);
v_e_1787_ = v___x_1837_;
goto _start;
}
else
{
size_t v___x_1839_; size_t v___x_1840_; uint8_t v___x_1841_; 
v___x_1839_ = lean_ptr_addr(v_value_1795_);
v___x_1840_ = lean_ptr_addr(v_val_1799_);
v___x_1841_ = lean_usize_dec_eq(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_inc_ref(v_body_1796_);
lean_inc_ref(v_type_1794_);
lean_inc(v_declName_1793_);
lean_dec_ref_known(v_e_1787_, 4);
v___x_1842_ = l_Lean_Expr_letE___override(v_declName_1793_, v_type_1794_, v_val_1799_, v_body_1796_, v_nondep_1797_);
v_e_1787_ = v___x_1842_;
goto _start;
}
else
{
size_t v___x_1844_; uint8_t v___x_1845_; 
v___x_1844_ = lean_ptr_addr(v_body_1796_);
v___x_1845_ = lean_usize_dec_eq(v___x_1844_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_inc_ref(v_body_1796_);
lean_inc_ref(v_type_1794_);
lean_inc(v_declName_1793_);
lean_dec_ref_known(v_e_1787_, 4);
v___x_1846_ = l_Lean_Expr_letE___override(v_declName_1793_, v_type_1794_, v_val_1799_, v_body_1796_, v_nondep_1797_);
v_e_1787_ = v___x_1846_;
goto _start;
}
else
{
lean_dec(v_val_1799_);
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_val_1799_);
lean_dec_ref_known(v_e_1787_, 4);
v_a_1849_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1800_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1800_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v___x_1857_; lean_object* v_num_1858_; uint8_t v___x_1859_; 
lean_dec(v___x_1798_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_num_1858_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1787_, v___x_1857_);
v___x_1859_ = lean_nat_dec_lt(v___x_1857_, v_num_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
lean_dec(v_num_1858_);
lean_dec_ref_known(v_e_1787_, 4);
v___x_1860_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4);
v___x_1861_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v___x_1860_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
return v___x_1861_;
}
else
{
lean_object* v___f_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; lean_object* v___x_1865_; 
v___f_1862_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed), 7, 0);
v___x_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_num_1858_);
v___x_1864_ = 0;
v___x_1865_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1787_, v___x_1863_, v___f_1862_, v___x_1864_, v___x_1859_, v___x_1864_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
lean_dec_ref_known(v___x_1863_, 1);
return v___x_1865_;
}
}
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_e_1787_);
return v___x_1866_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1787_ = stack[0].m_obj;
lean_object* v_a_1788_ = stack[1].m_obj;
lean_object* v_a_1789_ = stack[2].m_obj;
lean_object* v_a_1790_ = stack[3].m_obj;
lean_object* v_a_1791_ = stack[4].m_obj;
lean_object* v_res_1867_;
v_res_1867_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
stack->m_obj
 = v_res_1867_;
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object* v_xs_1868_, lean_object* v_b_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_b_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; uint8_t v___x_1877_; uint8_t v___x_1878_; lean_object* v___x_1879_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
lean_inc(v_a_1876_);
lean_dec_ref_known(v___x_1875_, 1);
v___x_1877_ = 0;
v___x_1878_ = 1;
v___x_1879_ = l_Lean_Meta_mkLetFVars(v_xs_1868_, v_a_1876_, v___x_1877_, v___x_1877_, v___x_1878_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
return v___x_1879_;
}
else
{
return v___x_1875_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_1868_ = stack[0].m_obj;
lean_object* v_b_1869_ = stack[1].m_obj;
lean_object* v___y_1870_ = stack[2].m_obj;
lean_object* v___y_1871_ = stack[3].m_obj;
lean_object* v___y_1872_ = stack[4].m_obj;
lean_object* v___y_1873_ = stack[5].m_obj;
lean_object* v_res_1880_;
v_res_1880_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1868_, v_b_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
stack->m_obj
 = v_res_1880_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object* v_e_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
return v_res_1887_;
}
}
lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object* v_e_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
uint8_t v___y_1895_; uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Expr_isLet(v_e_1888_);
if (v___x_1917_ == 0)
{
uint8_t v___x_1918_; 
v___x_1918_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1888_);
v___y_1895_ = v___x_1918_;
goto v___jp_1894_;
}
else
{
v___y_1895_ = v___x_1917_;
goto v___jp_1894_;
}
v___jp_1894_:
{
if (v___y_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; 
lean_dec_ref(v_e_1888_);
v___x_1896_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
return v___x_1897_;
}
else
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1908_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1901_ = v___x_1898_;
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1908_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_a_1899_);
v___x_1904_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1904_);
v___x_1906_ = v___x_1901_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
v_a_1909_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1898_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1898_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_paramLet___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1888_ = stack[0].m_obj;
lean_object* v_a_1889_ = stack[1].m_obj;
lean_object* v_a_1890_ = stack[2].m_obj;
lean_object* v_a_1891_ = stack[3].m_obj;
lean_object* v_a_1892_ = stack[4].m_obj;
lean_object* v_res_1919_;
v_res_1919_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
stack->m_obj
 = v_res_1919_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object* v_e_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v_res_1926_; 
v_res_1926_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_);
lean_dec(v_a_1924_);
lean_dec_ref(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec_ref(v_a_1921_);
return v_res_1926_;
}
}
lean_object* l_Lean_Elab_WF_paramLet(lean_object* v_e_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1927_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_paramLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1927_ = stack[0].m_obj;
lean_object* v_a_1928_ = stack[1].m_obj;
lean_object* v_a_1929_ = stack[2].m_obj;
lean_object* v_a_1930_ = stack[3].m_obj;
lean_object* v_a_1931_ = stack[4].m_obj;
lean_object* v_a_1932_ = stack[5].m_obj;
lean_object* v_a_1933_ = stack[6].m_obj;
lean_object* v_a_1934_ = stack[7].m_obj;
lean_object* v_res_1937_;
v_res_1937_ = l_Lean_Elab_WF_paramLet(v_e_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_);
stack->m_obj
 = v_res_1937_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object* v_e_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_Elab_WF_paramLet(v_e_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_);
lean_dec(v_a_1945_);
lean_dec_ref(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
return v_res_1947_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1955_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_));
v___x_1956_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_1957_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1958_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1955_, v___x_1956_, v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1959_;
v_res_1959_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_();
stack->m_obj
 = v_res_1959_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10____boxed(lean_object* v_a_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_();
return v_res_1961_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object* v_lctx_1962_, lean_object* v_x_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_keyedConfig_1969_; uint8_t v_trackZetaDelta_1970_; lean_object* v_zetaDeltaSet_1971_; lean_object* v_localInstances_1972_; lean_object* v_defEqCtx_x3f_1973_; lean_object* v_synthPendingDepth_1974_; lean_object* v_customCanUnfoldPredicate_x3f_1975_; uint8_t v_univApprox_1976_; uint8_t v_inTypeClassResolution_1977_; uint8_t v_cacheInferType_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_keyedConfig_1969_ = lean_ctor_get(v___y_1964_, 0);
v_trackZetaDelta_1970_ = lean_ctor_get_uint8(v___y_1964_, sizeof(void*)*7);
v_zetaDeltaSet_1971_ = lean_ctor_get(v___y_1964_, 1);
v_localInstances_1972_ = lean_ctor_get(v___y_1964_, 3);
v_defEqCtx_x3f_1973_ = lean_ctor_get(v___y_1964_, 4);
v_synthPendingDepth_1974_ = lean_ctor_get(v___y_1964_, 5);
v_customCanUnfoldPredicate_x3f_1975_ = lean_ctor_get(v___y_1964_, 6);
v_univApprox_1976_ = lean_ctor_get_uint8(v___y_1964_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1977_ = lean_ctor_get_uint8(v___y_1964_, sizeof(void*)*7 + 2);
v_cacheInferType_1978_ = lean_ctor_get_uint8(v___y_1964_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1975_);
lean_inc(v_synthPendingDepth_1974_);
lean_inc(v_defEqCtx_x3f_1973_);
lean_inc_ref(v_localInstances_1972_);
lean_inc(v_zetaDeltaSet_1971_);
lean_inc_ref(v_keyedConfig_1969_);
v___x_1979_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1979_, 0, v_keyedConfig_1969_);
lean_ctor_set(v___x_1979_, 1, v_zetaDeltaSet_1971_);
lean_ctor_set(v___x_1979_, 2, v_lctx_1962_);
lean_ctor_set(v___x_1979_, 3, v_localInstances_1972_);
lean_ctor_set(v___x_1979_, 4, v_defEqCtx_x3f_1973_);
lean_ctor_set(v___x_1979_, 5, v_synthPendingDepth_1974_);
lean_ctor_set(v___x_1979_, 6, v_customCanUnfoldPredicate_x3f_1975_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*7, v_trackZetaDelta_1970_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*7 + 1, v_univApprox_1976_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1977_);
lean_ctor_set_uint8(v___x_1979_, sizeof(void*)*7 + 3, v_cacheInferType_1978_);
lean_inc(v___y_1967_);
lean_inc_ref(v___y_1966_);
lean_inc(v___y_1965_);
v___x_1980_ = lean_apply_5(v_x_1963_, v___x_1979_, v___y_1965_, v___y_1966_, v___y_1967_, lean_box(0));
return v___x_1980_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1962_ = stack[0].m_obj;
lean_object* v_x_1963_ = stack[1].m_obj;
lean_object* v___y_1964_ = stack[2].m_obj;
lean_object* v___y_1965_ = stack[3].m_obj;
lean_object* v___y_1966_ = stack[4].m_obj;
lean_object* v___y_1967_ = stack[5].m_obj;
lean_object* v_res_1981_;
v_res_1981_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1962_, v_x_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
stack->m_obj
 = v_res_1981_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object* v_lctx_1982_, lean_object* v_x_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1982_, v_x_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
return v_res_1989_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object* v_00_u03b1_1990_, lean_object* v_lctx_1991_, lean_object* v_x_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1991_, v_x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1998_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1991_ = stack[1].m_obj;
lean_object* v_x_1992_ = stack[2].m_obj;
lean_object* v___y_1993_ = stack[3].m_obj;
lean_object* v___y_1994_ = stack[4].m_obj;
lean_object* v___y_1995_ = stack[5].m_obj;
lean_object* v___y_1996_ = stack[6].m_obj;
lean_object* v_res_1999_;
v_res_1999_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_box(0), v_lctx_1991_, v_x_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
stack->m_obj
 = v_res_1999_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object* v_00_u03b1_2000_, lean_object* v_lctx_2001_, lean_object* v_x_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(v_00_u03b1_2000_, v_lctx_2001_, v_x_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2008_;
}
}
lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object* v_e_2009_, lean_object* v_k_2010_, uint8_t v_cleanupAnnotations_2011_, uint8_t v_preserveNondepLet_2012_, uint8_t v_nondepLetOnly_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___f_2019_; uint8_t v___x_2020_; uint8_t v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___f_2019_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2019_, 0, v_k_2010_);
v___x_2020_ = 0;
v___x_2021_ = 1;
v___x_2022_ = lean_box(0);
v___x_2023_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_2009_, v___x_2020_, v___x_2021_, v_preserveNondepLet_2012_, v_nondepLetOnly_2013_, v___x_2022_, v___f_2019_, v_cleanupAnnotations_2011_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2023_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2023_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
v_a_2032_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2023_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2023_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2009_ = stack[0].m_obj;
lean_object* v_k_2010_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_2011_ = stack[2].m_num;
uint8_t v_preserveNondepLet_2012_ = stack[3].m_num;
uint8_t v_nondepLetOnly_2013_ = stack[4].m_num;
lean_object* v___y_2014_ = stack[5].m_obj;
lean_object* v___y_2015_ = stack[6].m_obj;
lean_object* v___y_2016_ = stack[7].m_obj;
lean_object* v___y_2017_ = stack[8].m_obj;
lean_object* v_res_2040_;
v_res_2040_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2009_, v_k_2010_, v_cleanupAnnotations_2011_, v_preserveNondepLet_2012_, v_nondepLetOnly_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
stack->m_obj
 = v_res_2040_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object* v_e_2041_, lean_object* v_k_2042_, lean_object* v_cleanupAnnotations_2043_, lean_object* v_preserveNondepLet_2044_, lean_object* v_nondepLetOnly_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2051_; uint8_t v_preserveNondepLet_boxed_2052_; uint8_t v_nondepLetOnly_boxed_2053_; lean_object* v_res_2054_; 
v_cleanupAnnotations_boxed_2051_ = lean_unbox(v_cleanupAnnotations_2043_);
v_preserveNondepLet_boxed_2052_ = lean_unbox(v_preserveNondepLet_2044_);
v_nondepLetOnly_boxed_2053_ = lean_unbox(v_nondepLetOnly_2045_);
v_res_2054_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2041_, v_k_2042_, v_cleanupAnnotations_boxed_2051_, v_preserveNondepLet_boxed_2052_, v_nondepLetOnly_boxed_2053_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
return v_res_2054_;
}
}
lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object* v_00_u03b1_2055_, lean_object* v_e_2056_, lean_object* v_k_2057_, uint8_t v_cleanupAnnotations_2058_, uint8_t v_preserveNondepLet_2059_, uint8_t v_nondepLetOnly_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2056_, v_k_2057_, v_cleanupAnnotations_2058_, v_preserveNondepLet_2059_, v_nondepLetOnly_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT void l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2056_ = stack[1].m_obj;
lean_object* v_k_2057_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_2058_ = stack[3].m_num;
uint8_t v_preserveNondepLet_2059_ = stack[4].m_num;
uint8_t v_nondepLetOnly_2060_ = stack[5].m_num;
lean_object* v___y_2061_ = stack[6].m_obj;
lean_object* v___y_2062_ = stack[7].m_obj;
lean_object* v___y_2063_ = stack[8].m_obj;
lean_object* v___y_2064_ = stack[9].m_obj;
lean_object* v_res_2067_;
v_res_2067_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_box(0), v_e_2056_, v_k_2057_, v_cleanupAnnotations_2058_, v_preserveNondepLet_2059_, v_nondepLetOnly_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
stack->m_obj
 = v_res_2067_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object* v_00_u03b1_2068_, lean_object* v_e_2069_, lean_object* v_k_2070_, lean_object* v_cleanupAnnotations_2071_, lean_object* v_preserveNondepLet_2072_, lean_object* v_nondepLetOnly_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2079_; uint8_t v_preserveNondepLet_boxed_2080_; uint8_t v_nondepLetOnly_boxed_2081_; lean_object* v_res_2082_; 
v_cleanupAnnotations_boxed_2079_ = lean_unbox(v_cleanupAnnotations_2071_);
v_preserveNondepLet_boxed_2080_ = lean_unbox(v_preserveNondepLet_2072_);
v_nondepLetOnly_boxed_2081_ = lean_unbox(v_nondepLetOnly_2073_);
v_res_2082_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(v_00_u03b1_2068_, v_e_2069_, v_k_2070_, v_cleanupAnnotations_boxed_2079_, v_preserveNondepLet_boxed_2080_, v_nondepLetOnly_boxed_2081_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
return v_res_2082_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object* v_e_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_e_2083_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2083_ = stack[0].m_obj;
lean_object* v___y_2084_ = stack[1].m_obj;
lean_object* v___y_2085_ = stack[2].m_obj;
lean_object* v___y_2086_ = stack[3].m_obj;
lean_object* v___y_2087_ = stack[4].m_obj;
lean_object* v_res_2091_;
v_res_2091_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
stack->m_obj
 = v_res_2091_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object* v_e_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2098_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object* v_as_2099_, size_t v_i_2100_, size_t v_stop_2101_, lean_object* v_b_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_usize_dec_eq(v_i_2100_, v_stop_2101_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = lean_array_uget_borrowed(v_as_2099_, v_i_2100_);
v___x_2110_ = l_Lean_Expr_fvarId_x21(v___x_2109_);
v___x_2111_ = l_Lean_FVarId_getDecl___redArg(v___x_2110_, v___y_2103_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; uint8_t v_a_2114_; uint8_t v___x_2120_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2120_ = l_Lean_LocalDecl_isNondep(v_a_2112_);
if (v___x_2120_ == 0)
{
v_a_2114_ = v___x_2120_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = l_Lean_LocalDecl_type(v_a_2112_);
v___x_2122_ = l_Lean_Meta_isProp(v___x_2121_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; uint8_t v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
v___x_2124_ = lean_unbox(v_a_2123_);
lean_dec(v_a_2123_);
v_a_2114_ = v___x_2124_;
goto v___jp_2113_;
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec(v_a_2112_);
lean_dec_ref(v_b_2102_);
v_a_2125_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2122_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2122_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
v___jp_2113_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; 
v___x_2115_ = l_Lean_LocalDecl_setNondep(v_a_2112_, v_a_2114_);
v___x_2116_ = l_Lean_LocalContext_addDecl(v_b_2102_, v___x_2115_);
v___x_2117_ = ((size_t)1ULL);
v___x_2118_ = lean_usize_add(v_i_2100_, v___x_2117_);
v_i_2100_ = v___x_2118_;
v_b_2102_ = v___x_2116_;
goto _start;
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec_ref(v_b_2102_);
v_a_2133_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2111_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2111_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_b_2102_);
return v___x_2141_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2099_ = stack[0].m_obj;
size_t v_i_2100_ = stack[1].m_num;
size_t v_stop_2101_ = stack[2].m_num;
lean_object* v_b_2102_ = stack[3].m_obj;
lean_object* v___y_2103_ = stack[4].m_obj;
lean_object* v___y_2104_ = stack[5].m_obj;
lean_object* v___y_2105_ = stack[6].m_obj;
lean_object* v___y_2106_ = stack[7].m_obj;
lean_object* v_res_2142_;
v_res_2142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2099_, v_i_2100_, v_stop_2101_, v_b_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object* v_as_2143_, lean_object* v_i_2144_, lean_object* v_stop_2145_, lean_object* v_b_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
size_t v_i_boxed_2152_; size_t v_stop_boxed_2153_; lean_object* v_res_2154_; 
v_i_boxed_2152_ = lean_unbox_usize(v_i_2144_);
lean_dec(v_i_2144_);
v_stop_boxed_2153_ = lean_unbox_usize(v_stop_2145_);
lean_dec(v_stop_2145_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2143_, v_i_boxed_2152_, v_stop_boxed_2153_, v_b_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec_ref(v_as_2143_);
return v_res_2154_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t v_a_2155_, lean_object* v_lctx_2156_, lean_object* v_xs_2157_, lean_object* v_b_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_a_2165_; lean_object* v___y_2173_; lean_object* v___x_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2183_ = lean_unsigned_to_nat(0u);
v___x_2184_ = lean_array_get_size(v_xs_2157_);
v___x_2185_ = lean_nat_dec_lt(v___x_2183_, v___x_2184_);
if (v___x_2185_ == 0)
{
v_a_2165_ = v_lctx_2156_;
goto v___jp_2164_;
}
else
{
uint8_t v___x_2186_; 
v___x_2186_ = lean_nat_dec_le(v___x_2184_, v___x_2184_);
if (v___x_2186_ == 0)
{
if (v___x_2185_ == 0)
{
v_a_2165_ = v_lctx_2156_;
goto v___jp_2164_;
}
else
{
size_t v___x_2187_; size_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = lean_usize_of_nat(v___x_2184_);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2157_, v___x_2187_, v___x_2188_, v_lctx_2156_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
v___y_2173_ = v___x_2189_;
goto v___jp_2172_;
}
}
else
{
size_t v___x_2190_; size_t v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((size_t)0ULL);
v___x_2191_ = lean_usize_of_nat(v___x_2184_);
v___x_2192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2157_, v___x_2190_, v___x_2191_, v_lctx_2156_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
v___y_2173_ = v___x_2192_;
goto v___jp_2172_;
}
}
v___jp_2164_:
{
uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2166_ = 1;
v___x_2167_ = lean_box(v_a_2155_);
v___x_2168_ = lean_box(v_a_2155_);
v___x_2169_ = lean_box(v___x_2166_);
v___x_2170_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2170_, 0, v_xs_2157_);
lean_closure_set(v___x_2170_, 1, v_b_2158_);
lean_closure_set(v___x_2170_, 2, v___x_2167_);
lean_closure_set(v___x_2170_, 3, v___x_2168_);
lean_closure_set(v___x_2170_, 4, v___x_2169_);
v___x_2171_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_a_2165_, v___x_2170_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2171_;
}
v___jp_2172_:
{
if (lean_obj_tag(v___y_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___y_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___y_2173_, 1);
v_a_2165_ = v_a_2174_;
goto v___jp_2164_;
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec_ref(v_b_2158_);
lean_dec_ref(v_xs_2157_);
v_a_2175_ = lean_ctor_get(v___y_2173_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___y_2173_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___y_2173_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___y_2173_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_2155_ = stack[0].m_num;
lean_object* v_lctx_2156_ = stack[1].m_obj;
lean_object* v_xs_2157_ = stack[2].m_obj;
lean_object* v_b_2158_ = stack[3].m_obj;
lean_object* v___y_2159_ = stack[4].m_obj;
lean_object* v___y_2160_ = stack[5].m_obj;
lean_object* v___y_2161_ = stack[6].m_obj;
lean_object* v___y_2162_ = stack[7].m_obj;
lean_object* v_res_2193_;
v_res_2193_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_2155_, v_lctx_2156_, v_xs_2157_, v_b_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
stack->m_obj
 = v_res_2193_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object* v_a_2194_, lean_object* v_lctx_2195_, lean_object* v_xs_2196_, lean_object* v_b_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
uint8_t v_a_10805__boxed_2203_; lean_object* v_res_2204_; 
v_a_10805__boxed_2203_ = lean_unbox(v_a_2194_);
v_res_2204_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_10805__boxed_2203_, v_lctx_2195_, v_xs_2196_, v_b_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2204_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object* v_e_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
lean_inc_ref(v_e_2205_);
v___x_2211_ = l_Lean_Meta_isProof(v_e_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2249_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2214_ = v___x_2211_;
v_isShared_2215_ = v_isSharedCheck_2249_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2211_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2249_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_unbox(v_a_2212_);
if (v___x_2216_ == 0)
{
uint8_t v___x_2217_; 
v___x_2217_ = l_Lean_Expr_isLet(v_e_2205_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_dec(v_a_2212_);
lean_dec_ref(v_e_2205_);
v___x_2218_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2218_);
v___x_2220_ = v___x_2214_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2218_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
else
{
lean_object* v_lctx_2222_; lean_object* v___f_2223_; uint8_t v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; 
lean_del_object(v___x_2214_);
v_lctx_2222_ = lean_ctor_get(v___y_2206_, 2);
lean_inc_ref(v_lctx_2222_);
lean_inc(v_a_2212_);
v___f_2223_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2223_, 0, v_a_2212_);
lean_closure_set(v___f_2223_, 1, v_lctx_2222_);
v___x_2224_ = lean_unbox(v_a_2212_);
v___x_2225_ = lean_unbox(v_a_2212_);
lean_dec(v_a_2212_);
v___x_2226_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2205_, v___f_2223_, v___x_2224_, v___x_2217_, v___x_2225_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2236_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2229_ = v___x_2226_;
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_a_2227_);
lean_dec(v___x_2226_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_a_2227_);
v___x_2232_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 0, v___x_2232_);
v___x_2234_ = v___x_2229_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_a_2237_ = lean_ctor_get(v___x_2226_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2226_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2226_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2226_);
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
}
else
{
lean_object* v___x_2245_; lean_object* v___x_2247_; 
lean_dec(v_a_2212_);
v___x_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2245_, 0, v_e_2205_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v___x_2245_);
v___x_2247_ = v___x_2214_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2245_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_dec_ref(v_e_2205_);
v_a_2250_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___x_2211_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2211_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2205_ = stack[0].m_obj;
lean_object* v___y_2206_ = stack[1].m_obj;
lean_object* v___y_2207_ = stack[2].m_obj;
lean_object* v___y_2208_ = stack[3].m_obj;
lean_object* v___y_2209_ = stack[4].m_obj;
lean_object* v_res_2258_;
v_res_2258_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
stack->m_obj
 = v_res_2258_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object* v_e_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
return v_res_2265_;
}
}
lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object* v_00_u03b1_2266_, lean_object* v_x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2273_ = lean_apply_1(v_x_2267_, lean_box(0));
v___x_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2267_ = stack[1].m_obj;
lean_object* v___y_2268_ = stack[2].m_obj;
lean_object* v___y_2269_ = stack[3].m_obj;
lean_object* v___y_2270_ = stack[4].m_obj;
lean_object* v___y_2271_ = stack[5].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v_x_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2276_, lean_object* v_x_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(v_00_u03b1_2276_, v_x_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2289_ = l_Lean_maxRecDepthErrorMessage;
v___x_2290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3);
v___x_2292_ = l_Lean_MessageData_ofFormat(v___x_2291_);
return v___x_2292_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4);
v___x_2294_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2));
v___x_2295_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v___x_2293_);
return v___x_2295_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object* v_ref_2296_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v_ref_2296_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2296_ = stack[0].m_obj;
lean_object* v_res_2301_;
v_res_2301_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2296_);
stack->m_obj
 = v_res_2301_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object* v_ref_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2302_);
return v_res_2304_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object* v_x_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___y_2313_; lean_object* v_toCold_2322_; lean_object* v_currRecDepth_2323_; lean_object* v_ref_2324_; uint16_t v_optionFlags_2325_; uint8_t v_suppressElabErrors_2326_; uint8_t v_isRecordingDeps_2327_; lean_object* v_maxRecDepth_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v_toCold_2322_ = lean_ctor_get(v___y_2309_, 0);
v_currRecDepth_2323_ = lean_ctor_get(v___y_2309_, 1);
v_ref_2324_ = lean_ctor_get(v___y_2309_, 2);
v_optionFlags_2325_ = lean_ctor_get_uint16(v___y_2309_, sizeof(void*)*3);
v_suppressElabErrors_2326_ = lean_ctor_get_uint8(v___y_2309_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2327_ = lean_ctor_get_uint8(v___y_2309_, sizeof(void*)*3 + 3);
v_maxRecDepth_2333_ = lean_ctor_get(v_toCold_2322_, 3);
v___x_2334_ = lean_unsigned_to_nat(0u);
v___x_2335_ = lean_nat_dec_eq(v_maxRecDepth_2333_, v___x_2334_);
if (v___x_2335_ == 0)
{
uint8_t v___x_2336_; 
v___x_2336_ = lean_nat_dec_eq(v_currRecDepth_2323_, v_maxRecDepth_2333_);
if (v___x_2336_ == 0)
{
goto v___jp_2328_;
}
else
{
lean_object* v___x_2337_; 
lean_dec_ref(v_x_2305_);
lean_inc(v_ref_2324_);
v___x_2337_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2324_);
v___y_2313_ = v___x_2337_;
goto v___jp_2312_;
}
}
else
{
goto v___jp_2328_;
}
v___jp_2312_:
{
if (lean_obj_tag(v___y_2313_) == 0)
{
return v___y_2313_;
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2314_ = lean_ctor_get(v___y_2313_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___y_2313_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___y_2313_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___y_2313_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
v___jp_2328_:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = lean_unsigned_to_nat(1u);
v___x_2330_ = lean_nat_add(v_currRecDepth_2323_, v___x_2329_);
lean_inc(v_ref_2324_);
lean_inc_ref(v_toCold_2322_);
v___x_2331_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2331_, 0, v_toCold_2322_);
lean_ctor_set(v___x_2331_, 1, v___x_2330_);
lean_ctor_set(v___x_2331_, 2, v_ref_2324_);
lean_ctor_set_uint16(v___x_2331_, sizeof(void*)*3, v_optionFlags_2325_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*3 + 2, v_suppressElabErrors_2326_);
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*3 + 3, v_isRecordingDeps_2327_);
lean_inc(v___y_2310_);
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
lean_inc(v___y_2306_);
v___x_2332_ = lean_apply_6(v_x_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___x_2331_, v___y_2310_, lean_box(0));
v___y_2313_ = v___x_2332_;
goto v___jp_2312_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2305_ = stack[0].m_obj;
lean_object* v___y_2306_ = stack[1].m_obj;
lean_object* v___y_2307_ = stack[2].m_obj;
lean_object* v___y_2308_ = stack[3].m_obj;
lean_object* v___y_2309_ = stack[4].m_obj;
lean_object* v___y_2310_ = stack[5].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec(v___y_2340_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object* v_a_2347_, lean_object* v_x_2348_){
_start:
{
if (lean_obj_tag(v_x_2348_) == 0)
{
lean_object* v___x_2349_; 
v___x_2349_ = lean_box(0);
return v___x_2349_;
}
else
{
lean_object* v_key_2350_; lean_object* v_value_2351_; lean_object* v_tail_2352_; uint8_t v___x_2353_; 
v_key_2350_ = lean_ctor_get(v_x_2348_, 0);
v_value_2351_ = lean_ctor_get(v_x_2348_, 1);
v_tail_2352_ = lean_ctor_get(v_x_2348_, 2);
v___x_2353_ = l_Lean_ExprStructEq_beq(v_key_2350_, v_a_2347_);
if (v___x_2353_ == 0)
{
v_x_2348_ = v_tail_2352_;
goto _start;
}
else
{
lean_object* v___x_2355_; 
lean_inc(v_value_2351_);
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v_value_2351_);
return v___x_2355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_a_2356_, lean_object* v_x_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2356_, v_x_2357_);
lean_dec(v_x_2357_);
lean_dec_ref(v_a_2356_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_m_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_buckets_2361_; lean_object* v___x_2362_; uint64_t v___x_2363_; uint64_t v___x_2364_; uint64_t v___x_2365_; uint64_t v_fold_2366_; uint64_t v___x_2367_; uint64_t v___x_2368_; uint64_t v___x_2369_; size_t v___x_2370_; size_t v___x_2371_; size_t v___x_2372_; size_t v___x_2373_; size_t v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_buckets_2361_ = lean_ctor_get(v_m_2359_, 1);
v___x_2362_ = lean_array_get_size(v_buckets_2361_);
v___x_2363_ = l_Lean_ExprStructEq_hash(v_a_2360_);
v___x_2364_ = 32ULL;
v___x_2365_ = lean_uint64_shift_right(v___x_2363_, v___x_2364_);
v_fold_2366_ = lean_uint64_xor(v___x_2363_, v___x_2365_);
v___x_2367_ = 16ULL;
v___x_2368_ = lean_uint64_shift_right(v_fold_2366_, v___x_2367_);
v___x_2369_ = lean_uint64_xor(v_fold_2366_, v___x_2368_);
v___x_2370_ = lean_uint64_to_usize(v___x_2369_);
v___x_2371_ = lean_usize_of_nat(v___x_2362_);
v___x_2372_ = ((size_t)1ULL);
v___x_2373_ = lean_usize_sub(v___x_2371_, v___x_2372_);
v___x_2374_ = lean_usize_land(v___x_2370_, v___x_2373_);
v___x_2375_ = lean_array_uget_borrowed(v_buckets_2361_, v___x_2374_);
v___x_2376_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2360_, v___x_2375_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_m_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_2377_, v_a_2378_);
lean_dec_ref(v_a_2378_);
lean_dec_ref(v_m_2377_);
return v_res_2379_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2380_, lean_object* v___y_2381_, lean_object* v_b_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2381_);
v___x_2388_ = lean_apply_7(v_k_2380_, v_b_2382_, v___y_2381_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, lean_box(0));
return v___x_2388_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2380_ = stack[0].m_obj;
lean_object* v___y_2381_ = stack[1].m_obj;
lean_object* v_b_2382_ = stack[2].m_obj;
lean_object* v___y_2383_ = stack[3].m_obj;
lean_object* v___y_2384_ = stack[4].m_obj;
lean_object* v___y_2385_ = stack[5].m_obj;
lean_object* v___y_2386_ = stack[6].m_obj;
lean_object* v_res_2389_;
v_res_2389_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2380_, v___y_2381_, v_b_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
stack->m_obj
 = v_res_2389_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2390_, lean_object* v___y_2391_, lean_object* v_b_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2390_, v___y_2391_, v_b_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2391_);
return v_res_2398_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2399_, uint8_t v_bi_2400_, lean_object* v_type_2401_, lean_object* v_k_2402_, uint8_t v_kind_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___f_2410_; lean_object* v___x_2411_; 
lean_inc(v___y_2404_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2410_, 0, v_k_2402_);
lean_closure_set(v___f_2410_, 1, v___y_2404_);
v___x_2411_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2399_, v_bi_2400_, v_type_2401_, v___f_2410_, v_kind_2403_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2411_) == 0)
{
return v___x_2411_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2411_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2411_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2399_ = stack[0].m_obj;
uint8_t v_bi_2400_ = stack[1].m_num;
lean_object* v_type_2401_ = stack[2].m_obj;
lean_object* v_k_2402_ = stack[3].m_obj;
uint8_t v_kind_2403_ = stack[4].m_num;
lean_object* v___y_2404_ = stack[5].m_obj;
lean_object* v___y_2405_ = stack[6].m_obj;
lean_object* v___y_2406_ = stack[7].m_obj;
lean_object* v___y_2407_ = stack[8].m_obj;
lean_object* v___y_2408_ = stack[9].m_obj;
lean_object* v_res_2420_;
v_res_2420_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2399_, v_bi_2400_, v_type_2401_, v_k_2402_, v_kind_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
stack->m_obj
 = v_res_2420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2421_, lean_object* v_bi_2422_, lean_object* v_type_2423_, lean_object* v_k_2424_, lean_object* v_kind_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint8_t v_bi_boxed_2432_; uint8_t v_kind_boxed_2433_; lean_object* v_res_2434_; 
v_bi_boxed_2432_ = lean_unbox(v_bi_2422_);
v_kind_boxed_2433_ = lean_unbox(v_kind_2425_);
v_res_2434_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2421_, v_bi_boxed_2432_, v_type_2423_, v_k_2424_, v_kind_boxed_2433_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
return v_res_2434_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object* v___x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2435_);
return v___x_2441_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2435_ = stack[0].m_obj;
lean_object* v___y_2436_ = stack[1].m_obj;
lean_object* v___y_2437_ = stack[2].m_obj;
lean_object* v___y_2438_ = stack[3].m_obj;
lean_object* v___y_2439_ = stack[4].m_obj;
lean_object* v_res_2442_;
v_res_2442_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
stack->m_obj
 = v_res_2442_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
return v_res_2449_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2450_, lean_object* v_type_2451_, lean_object* v_val_2452_, lean_object* v_k_2453_, uint8_t v_nondep_2454_, uint8_t v_kind_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___f_2462_; lean_object* v___x_2463_; 
lean_inc(v___y_2456_);
v___f_2462_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2462_, 0, v_k_2453_);
lean_closure_set(v___f_2462_, 1, v___y_2456_);
v___x_2463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2450_, v_type_2451_, v_val_2452_, v___f_2462_, v_nondep_2454_, v_kind_2455_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2463_) == 0)
{
return v___x_2463_;
}
else
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
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2450_ = stack[0].m_obj;
lean_object* v_type_2451_ = stack[1].m_obj;
lean_object* v_val_2452_ = stack[2].m_obj;
lean_object* v_k_2453_ = stack[3].m_obj;
uint8_t v_nondep_2454_ = stack[4].m_num;
uint8_t v_kind_2455_ = stack[5].m_num;
lean_object* v___y_2456_ = stack[6].m_obj;
lean_object* v___y_2457_ = stack[7].m_obj;
lean_object* v___y_2458_ = stack[8].m_obj;
lean_object* v___y_2459_ = stack[9].m_obj;
lean_object* v___y_2460_ = stack[10].m_obj;
lean_object* v_res_2472_;
v_res_2472_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2450_, v_type_2451_, v_val_2452_, v_k_2453_, v_nondep_2454_, v_kind_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
stack->m_obj
 = v_res_2472_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2473_, lean_object* v_type_2474_, lean_object* v_val_2475_, lean_object* v_k_2476_, lean_object* v_nondep_2477_, lean_object* v_kind_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
uint8_t v_nondep_boxed_2485_; uint8_t v_kind_boxed_2486_; lean_object* v_res_2487_; 
v_nondep_boxed_2485_ = lean_unbox(v_nondep_2477_);
v_kind_boxed_2486_ = lean_unbox(v_kind_2478_);
v_res_2487_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2473_, v_type_2474_, v_val_2475_, v_k_2476_, v_nondep_boxed_2485_, v_kind_boxed_2486_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
return v_res_2487_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2488_, lean_object* v_x_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_apply_1(v_x_2489_, lean_box(0));
v___x_2496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2489_ = stack[1].m_obj;
lean_object* v___y_2490_ = stack[2].m_obj;
lean_object* v___y_2491_ = stack[3].m_obj;
lean_object* v___y_2492_ = stack[4].m_obj;
lean_object* v___y_2493_ = stack[5].m_obj;
lean_object* v_res_2497_;
v_res_2497_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v_x_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
stack->m_obj
 = v_res_2497_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_x_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2498_, v_x_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
return v_res_2505_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2506_, lean_object* v_x_2507_){
_start:
{
if (lean_obj_tag(v_x_2507_) == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = 0;
return v___x_2508_;
}
else
{
lean_object* v_key_2509_; lean_object* v_tail_2510_; uint8_t v___x_2511_; 
v_key_2509_ = lean_ctor_get(v_x_2507_, 0);
v_tail_2510_ = lean_ctor_get(v_x_2507_, 2);
v___x_2511_ = l_Lean_ExprStructEq_beq(v_key_2509_, v_a_2506_);
if (v___x_2511_ == 0)
{
v_x_2507_ = v_tail_2510_;
goto _start;
}
else
{
return v___x_2511_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2506_ = stack[0].m_obj;
lean_object* v_x_2507_ = stack[1].m_obj;
uint8_t v_res_2513_;
v_res_2513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2506_, v_x_2507_);
stack->m_num = v_res_2513_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2514_, lean_object* v_x_2515_){
_start:
{
uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_res_2516_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2514_, v_x_2515_);
lean_dec(v_x_2515_);
lean_dec_ref(v_a_2514_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2518_, lean_object* v_b_2519_, lean_object* v_x_2520_){
_start:
{
if (lean_obj_tag(v_x_2520_) == 0)
{
lean_dec(v_b_2519_);
lean_dec_ref(v_a_2518_);
return v_x_2520_;
}
else
{
lean_object* v_key_2521_; lean_object* v_value_2522_; lean_object* v_tail_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2535_; 
v_key_2521_ = lean_ctor_get(v_x_2520_, 0);
v_value_2522_ = lean_ctor_get(v_x_2520_, 1);
v_tail_2523_ = lean_ctor_get(v_x_2520_, 2);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_x_2520_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2525_ = v_x_2520_;
v_isShared_2526_ = v_isSharedCheck_2535_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_tail_2523_);
lean_inc(v_value_2522_);
lean_inc(v_key_2521_);
lean_dec(v_x_2520_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2535_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
uint8_t v___x_2527_; 
v___x_2527_ = l_Lean_ExprStructEq_beq(v_key_2521_, v_a_2518_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2518_, v_b_2519_, v_tail_2523_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 2, v___x_2528_);
v___x_2530_ = v___x_2525_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_key_2521_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_value_2522_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
else
{
lean_object* v___x_2533_; 
lean_dec(v_value_2522_);
lean_dec(v_key_2521_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 1, v_b_2519_);
lean_ctor_set(v___x_2525_, 0, v_a_2518_);
v___x_2533_ = v___x_2525_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2518_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v_b_2519_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_tail_2523_);
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
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2536_, lean_object* v_x_2537_){
_start:
{
if (lean_obj_tag(v_x_2537_) == 0)
{
return v_x_2536_;
}
else
{
lean_object* v_key_2538_; lean_object* v_value_2539_; lean_object* v_tail_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2563_; 
v_key_2538_ = lean_ctor_get(v_x_2537_, 0);
v_value_2539_ = lean_ctor_get(v_x_2537_, 1);
v_tail_2540_ = lean_ctor_get(v_x_2537_, 2);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_x_2537_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2542_ = v_x_2537_;
v_isShared_2543_ = v_isSharedCheck_2563_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_tail_2540_);
lean_inc(v_value_2539_);
lean_inc(v_key_2538_);
lean_dec(v_x_2537_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2563_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; uint64_t v___x_2545_; uint64_t v___x_2546_; uint64_t v___x_2547_; uint64_t v_fold_2548_; uint64_t v___x_2549_; uint64_t v___x_2550_; uint64_t v___x_2551_; size_t v___x_2552_; size_t v___x_2553_; size_t v___x_2554_; size_t v___x_2555_; size_t v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2544_ = lean_array_get_size(v_x_2536_);
v___x_2545_ = l_Lean_ExprStructEq_hash(v_key_2538_);
v___x_2546_ = 32ULL;
v___x_2547_ = lean_uint64_shift_right(v___x_2545_, v___x_2546_);
v_fold_2548_ = lean_uint64_xor(v___x_2545_, v___x_2547_);
v___x_2549_ = 16ULL;
v___x_2550_ = lean_uint64_shift_right(v_fold_2548_, v___x_2549_);
v___x_2551_ = lean_uint64_xor(v_fold_2548_, v___x_2550_);
v___x_2552_ = lean_uint64_to_usize(v___x_2551_);
v___x_2553_ = lean_usize_of_nat(v___x_2544_);
v___x_2554_ = ((size_t)1ULL);
v___x_2555_ = lean_usize_sub(v___x_2553_, v___x_2554_);
v___x_2556_ = lean_usize_land(v___x_2552_, v___x_2555_);
v___x_2557_ = lean_array_uget_borrowed(v_x_2536_, v___x_2556_);
lean_inc(v___x_2557_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 2, v___x_2557_);
v___x_2559_ = v___x_2542_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_key_2538_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_value_2539_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_array_uset(v_x_2536_, v___x_2556_, v___x_2559_);
v_x_2536_ = v___x_2560_;
v_x_2537_ = v_tail_2540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2564_, lean_object* v_source_2565_, lean_object* v_target_2566_){
_start:
{
lean_object* v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = lean_array_get_size(v_source_2565_);
v___x_2568_ = lean_nat_dec_lt(v_i_2564_, v___x_2567_);
if (v___x_2568_ == 0)
{
lean_dec_ref(v_source_2565_);
lean_dec(v_i_2564_);
return v_target_2566_;
}
else
{
lean_object* v_es_2569_; lean_object* v___x_2570_; lean_object* v_source_2571_; lean_object* v_target_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_es_2569_ = lean_array_fget(v_source_2565_, v_i_2564_);
v___x_2570_ = lean_box(0);
v_source_2571_ = lean_array_fset(v_source_2565_, v_i_2564_, v___x_2570_);
v_target_2572_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2566_, v_es_2569_);
v___x_2573_ = lean_unsigned_to_nat(1u);
v___x_2574_ = lean_nat_add(v_i_2564_, v___x_2573_);
lean_dec(v_i_2564_);
v_i_2564_ = v___x_2574_;
v_source_2565_ = v_source_2571_;
v_target_2566_ = v_target_2572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2576_){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_nbuckets_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2577_ = lean_array_get_size(v_data_2576_);
v___x_2578_ = lean_unsigned_to_nat(2u);
v_nbuckets_2579_ = lean_nat_mul(v___x_2577_, v___x_2578_);
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = lean_box(0);
v___x_2582_ = lean_mk_array(v_nbuckets_2579_, v___x_2581_);
v___x_2583_ = lean_array_propagate_mark(v_data_2576_, v___x_2582_);
v___x_2584_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2580_, v_data_2576_, v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2585_, lean_object* v_a_2586_, lean_object* v_b_2587_){
_start:
{
lean_object* v_size_2588_; lean_object* v_buckets_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2632_; 
v_size_2588_ = lean_ctor_get(v_m_2585_, 0);
v_buckets_2589_ = lean_ctor_get(v_m_2585_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_m_2585_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2591_ = v_m_2585_;
v_isShared_2592_ = v_isSharedCheck_2632_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_buckets_2589_);
lean_inc(v_size_2588_);
lean_dec(v_m_2585_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2632_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; uint64_t v___x_2594_; uint64_t v___x_2595_; uint64_t v___x_2596_; uint64_t v_fold_2597_; uint64_t v___x_2598_; uint64_t v___x_2599_; uint64_t v___x_2600_; size_t v___x_2601_; size_t v___x_2602_; size_t v___x_2603_; size_t v___x_2604_; size_t v___x_2605_; lean_object* v_bkt_2606_; uint8_t v___x_2607_; 
v___x_2593_ = lean_array_get_size(v_buckets_2589_);
v___x_2594_ = l_Lean_ExprStructEq_hash(v_a_2586_);
v___x_2595_ = 32ULL;
v___x_2596_ = lean_uint64_shift_right(v___x_2594_, v___x_2595_);
v_fold_2597_ = lean_uint64_xor(v___x_2594_, v___x_2596_);
v___x_2598_ = 16ULL;
v___x_2599_ = lean_uint64_shift_right(v_fold_2597_, v___x_2598_);
v___x_2600_ = lean_uint64_xor(v_fold_2597_, v___x_2599_);
v___x_2601_ = lean_uint64_to_usize(v___x_2600_);
v___x_2602_ = lean_usize_of_nat(v___x_2593_);
v___x_2603_ = ((size_t)1ULL);
v___x_2604_ = lean_usize_sub(v___x_2602_, v___x_2603_);
v___x_2605_ = lean_usize_land(v___x_2601_, v___x_2604_);
v_bkt_2606_ = lean_array_uget_borrowed(v_buckets_2589_, v___x_2605_);
v___x_2607_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2586_, v_bkt_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v_size_x27_2609_; lean_object* v___x_2610_; lean_object* v_buckets_x27_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2608_ = lean_unsigned_to_nat(1u);
v_size_x27_2609_ = lean_nat_add(v_size_2588_, v___x_2608_);
lean_dec(v_size_2588_);
lean_inc(v_bkt_2606_);
v___x_2610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2610_, 0, v_a_2586_);
lean_ctor_set(v___x_2610_, 1, v_b_2587_);
lean_ctor_set(v___x_2610_, 2, v_bkt_2606_);
v_buckets_x27_2611_ = lean_array_uset(v_buckets_2589_, v___x_2605_, v___x_2610_);
v___x_2612_ = lean_unsigned_to_nat(4u);
v___x_2613_ = lean_nat_mul(v_size_x27_2609_, v___x_2612_);
v___x_2614_ = lean_unsigned_to_nat(3u);
v___x_2615_ = lean_nat_div(v___x_2613_, v___x_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_array_get_size(v_buckets_x27_2611_);
v___x_2617_ = lean_nat_dec_le(v___x_2615_, v___x_2616_);
lean_dec(v___x_2615_);
if (v___x_2617_ == 0)
{
lean_object* v_val_2618_; lean_object* v___x_2620_; 
v_val_2618_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2611_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v_val_2618_);
lean_ctor_set(v___x_2591_, 0, v_size_x27_2609_);
v___x_2620_ = v___x_2591_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_size_x27_2609_);
lean_ctor_set(v_reuseFailAlloc_2621_, 1, v_val_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v___x_2623_; 
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v_buckets_x27_2611_);
lean_ctor_set(v___x_2591_, 0, v_size_x27_2609_);
v___x_2623_ = v___x_2591_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_size_x27_2609_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_buckets_x27_2611_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
else
{
lean_object* v___x_2625_; lean_object* v_buckets_x27_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2630_; 
lean_inc(v_bkt_2606_);
v___x_2625_ = lean_box(0);
v_buckets_x27_2626_ = lean_array_uset(v_buckets_2589_, v___x_2605_, v___x_2625_);
v___x_2627_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2586_, v_b_2587_, v_bkt_2606_);
v___x_2628_ = lean_array_uset(v_buckets_x27_2626_, v___x_2605_, v___x_2627_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 1, v___x_2628_);
v___x_2630_ = v___x_2591_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_size_2588_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2633_, lean_object* v_e_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2637_ = lean_st_ref_take(v_a_2633_);
v___x_2638_ = lean_box(0);
v___x_2639_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2637_, v_e_2634_, v_a_2635_);
v___x_2640_ = lean_st_ref_put(v_a_2633_, v___x_2639_);
return v___x_2638_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2633_ = stack[0].m_obj;
lean_object* v_e_2634_ = stack[1].m_obj;
lean_object* v_a_2635_ = stack[2].m_obj;
lean_object* v_res_2641_;
v_res_2641_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2633_, v_e_2634_, v_a_2635_);
stack->m_obj
 = v_res_2641_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2642_, lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2642_, v_e_2643_, v_a_2644_);
lean_dec(v_a_2642_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_2647_, lean_object* v_pre_2648_, lean_object* v_post_2649_, lean_object* v_usedLetOnly_2650_, lean_object* v_skipConstInApp_2651_, lean_object* v_skipInstances_2652_, lean_object* v_body_2653_, lean_object* v_x_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
uint8_t v_usedLetOnly_boxed_2661_; uint8_t v_skipConstInApp_boxed_2662_; uint8_t v_skipInstances_boxed_2663_; lean_object* v_res_2664_; 
v_usedLetOnly_boxed_2661_ = lean_unbox(v_usedLetOnly_2650_);
v_skipConstInApp_boxed_2662_ = lean_unbox(v_skipConstInApp_2651_);
v_skipInstances_boxed_2663_ = lean_unbox(v_skipInstances_2652_);
v_res_2664_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_2647_, v_pre_2648_, v_post_2649_, v_usedLetOnly_boxed_2661_, v_skipConstInApp_boxed_2662_, v_skipInstances_boxed_2663_, v_body_2653_, v_x_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
return v_res_2664_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2668_, lean_object* v_pre_2669_, lean_object* v_post_2670_, uint8_t v_usedLetOnly_2671_, uint8_t v_skipConstInApp_2672_, uint8_t v_skipInstances_2673_, lean_object* v_body_2674_, lean_object* v_x_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_array_push(v_fvars_2668_, v_x_2675_);
v___x_2683_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2669_, v_post_2670_, v_usedLetOnly_2671_, v_skipConstInApp_2672_, v_skipInstances_2673_, v___x_2682_, v_body_2674_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
return v___x_2683_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2668_ = stack[0].m_obj;
lean_object* v_pre_2669_ = stack[1].m_obj;
lean_object* v_post_2670_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2671_ = stack[3].m_num;
uint8_t v_skipConstInApp_2672_ = stack[4].m_num;
uint8_t v_skipInstances_2673_ = stack[5].m_num;
lean_object* v_body_2674_ = stack[6].m_obj;
lean_object* v_x_2675_ = stack[7].m_obj;
lean_object* v___y_2676_ = stack[8].m_obj;
lean_object* v___y_2677_ = stack[9].m_obj;
lean_object* v___y_2678_ = stack[10].m_obj;
lean_object* v___y_2679_ = stack[11].m_obj;
lean_object* v___y_2680_ = stack[12].m_obj;
lean_object* v_res_2684_;
v_res_2684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2668_, v_pre_2669_, v_post_2670_, v_usedLetOnly_2671_, v_skipConstInApp_2672_, v_skipInstances_2673_, v_body_2674_, v_x_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
stack->m_obj
 = v_res_2684_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2685_, lean_object* v_pre_2686_, lean_object* v_post_2687_, lean_object* v_usedLetOnly_2688_, lean_object* v_skipConstInApp_2689_, lean_object* v_skipInstances_2690_, lean_object* v_body_2691_, lean_object* v_x_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v_usedLetOnly_boxed_2699_; uint8_t v_skipConstInApp_boxed_2700_; uint8_t v_skipInstances_boxed_2701_; lean_object* v_res_2702_; 
v_usedLetOnly_boxed_2699_ = lean_unbox(v_usedLetOnly_2688_);
v_skipConstInApp_boxed_2700_ = lean_unbox(v_skipConstInApp_2689_);
v_skipInstances_boxed_2701_ = lean_unbox(v_skipInstances_2690_);
v_res_2702_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2685_, v_pre_2686_, v_post_2687_, v_usedLetOnly_boxed_2699_, v_skipConstInApp_boxed_2700_, v_skipInstances_boxed_2701_, v_body_2691_, v_x_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
return v_res_2702_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2703_, lean_object* v_post_2704_, uint8_t v_usedLetOnly_2705_, uint8_t v_skipConstInApp_2706_, uint8_t v_skipInstances_2707_, lean_object* v_e_2708_, lean_object* v_a_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
lean_inc_ref(v_post_2704_);
lean_inc(v___y_2713_);
lean_inc_ref(v___y_2712_);
lean_inc(v___y_2711_);
lean_inc_ref(v___y_2710_);
lean_inc_ref(v_e_2708_);
v___x_2715_ = lean_apply_6(v_post_2704_, v_e_2708_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, lean_box(0));
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2734_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2734_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2734_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
switch(lean_obj_tag(v_a_2716_))
{
case 0:
{
lean_object* v_e_2720_; lean_object* v___x_2722_; 
lean_dec_ref(v_e_2708_);
lean_dec_ref(v_post_2704_);
lean_dec_ref(v_pre_2703_);
v_e_2720_ = lean_ctor_get(v_a_2716_, 0);
lean_inc_ref(v_e_2720_);
lean_dec_ref_known(v_a_2716_, 1);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_e_2720_);
v___x_2722_ = v___x_2718_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_e_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
case 1:
{
lean_object* v_e_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2718_);
lean_dec_ref(v_e_2708_);
v_e_2724_ = lean_ctor_get(v_a_2716_, 0);
lean_inc_ref(v_e_2724_);
lean_dec_ref_known(v_a_2716_, 1);
v___x_2725_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2703_, v_post_2704_, v_usedLetOnly_2705_, v_skipConstInApp_2706_, v_skipInstances_2707_, v_e_2724_, v_a_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v___x_2725_;
}
default: 
{
lean_object* v_e_x3f_2726_; 
lean_dec_ref(v_post_2704_);
lean_dec_ref(v_pre_2703_);
v_e_x3f_2726_ = lean_ctor_get(v_a_2716_, 0);
lean_inc(v_e_x3f_2726_);
lean_dec_ref_known(v_a_2716_, 1);
if (lean_obj_tag(v_e_x3f_2726_) == 0)
{
lean_object* v___x_2728_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_e_2708_);
v___x_2728_ = v___x_2718_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_e_2708_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
else
{
lean_object* v_val_2730_; lean_object* v___x_2732_; 
lean_dec_ref(v_e_2708_);
v_val_2730_ = lean_ctor_get(v_e_x3f_2726_, 0);
lean_inc(v_val_2730_);
lean_dec_ref_known(v_e_x3f_2726_, 1);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_val_2730_);
v___x_2732_ = v___x_2718_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_val_2730_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v_e_2708_);
lean_dec_ref(v_post_2704_);
lean_dec_ref(v_pre_2703_);
v_a_2735_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2715_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2715_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2703_ = stack[0].m_obj;
lean_object* v_post_2704_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2705_ = stack[2].m_num;
uint8_t v_skipConstInApp_2706_ = stack[3].m_num;
uint8_t v_skipInstances_2707_ = stack[4].m_num;
lean_object* v_e_2708_ = stack[5].m_obj;
lean_object* v_a_2709_ = stack[6].m_obj;
lean_object* v___y_2710_ = stack[7].m_obj;
lean_object* v___y_2711_ = stack[8].m_obj;
lean_object* v___y_2712_ = stack[9].m_obj;
lean_object* v___y_2713_ = stack[10].m_obj;
lean_object* v_res_2743_;
v_res_2743_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2703_, v_post_2704_, v_usedLetOnly_2705_, v_skipConstInApp_2706_, v_skipInstances_2707_, v_e_2708_, v_a_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
stack->m_obj
 = v_res_2743_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2744_, lean_object* v_post_2745_, uint8_t v_usedLetOnly_2746_, uint8_t v_skipConstInApp_2747_, uint8_t v_skipInstances_2748_, lean_object* v_fvars_2749_, lean_object* v_e_2750_, lean_object* v_a_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
if (lean_obj_tag(v_e_2750_) == 6)
{
lean_object* v_binderName_2757_; lean_object* v_binderType_2758_; lean_object* v_body_2759_; uint8_t v_binderInfo_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v_binderName_2757_ = lean_ctor_get(v_e_2750_, 0);
lean_inc(v_binderName_2757_);
v_binderType_2758_ = lean_ctor_get(v_e_2750_, 1);
lean_inc_ref(v_binderType_2758_);
v_body_2759_ = lean_ctor_get(v_e_2750_, 2);
lean_inc_ref(v_body_2759_);
v_binderInfo_2760_ = lean_ctor_get_uint8(v_e_2750_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2750_, 3);
v___x_2761_ = lean_box(v_usedLetOnly_2746_);
v___x_2762_ = lean_box(v_skipConstInApp_2747_);
v___x_2763_ = lean_box(v_skipInstances_2748_);
lean_inc_ref(v_post_2745_);
lean_inc_ref(v_pre_2744_);
lean_inc_ref(v_fvars_2749_);
v___f_2764_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2764_, 0, v_fvars_2749_);
lean_closure_set(v___f_2764_, 1, v_pre_2744_);
lean_closure_set(v___f_2764_, 2, v_post_2745_);
lean_closure_set(v___f_2764_, 3, v___x_2761_);
lean_closure_set(v___f_2764_, 4, v___x_2762_);
lean_closure_set(v___f_2764_, 5, v___x_2763_);
lean_closure_set(v___f_2764_, 6, v_body_2759_);
v___x_2765_ = lean_expr_instantiate_rev(v_binderType_2758_, v_fvars_2749_);
lean_dec_ref(v_fvars_2749_);
lean_dec_ref(v_binderType_2758_);
v___x_2766_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2744_, v_post_2745_, v_usedLetOnly_2746_, v_skipConstInApp_2747_, v_skipInstances_2748_, v___x_2765_, v_a_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = 0;
v___x_2769_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2757_, v_binderInfo_2760_, v_a_2767_, v___f_2764_, v___x_2768_, v_a_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2769_;
}
else
{
lean_dec_ref(v___f_2764_);
lean_dec(v_binderName_2757_);
return v___x_2766_;
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_expr_instantiate_rev(v_e_2750_, v_fvars_2749_);
lean_dec_ref(v_e_2750_);
lean_inc_ref(v_post_2745_);
lean_inc_ref(v_pre_2744_);
v___x_2771_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2744_, v_post_2745_, v_usedLetOnly_2746_, v_skipConstInApp_2747_, v_skipInstances_2748_, v___x_2770_, v_a_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; uint8_t v___x_2773_; uint8_t v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = 0;
v___x_2774_ = 1;
v___x_2775_ = 1;
v___x_2776_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2749_, v_a_2772_, v___x_2773_, v_usedLetOnly_2746_, v___x_2773_, v___x_2774_, v___x_2775_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec_ref(v_fvars_2749_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2744_, v_post_2745_, v_usedLetOnly_2746_, v_skipConstInApp_2747_, v_skipInstances_2748_, v_a_2777_, v_a_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
return v___x_2778_;
}
else
{
lean_dec_ref(v_post_2745_);
lean_dec_ref(v_pre_2744_);
return v___x_2776_;
}
}
else
{
lean_dec_ref(v_fvars_2749_);
lean_dec_ref(v_post_2745_);
lean_dec_ref(v_pre_2744_);
return v___x_2771_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2744_ = stack[0].m_obj;
lean_object* v_post_2745_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2746_ = stack[2].m_num;
uint8_t v_skipConstInApp_2747_ = stack[3].m_num;
uint8_t v_skipInstances_2748_ = stack[4].m_num;
lean_object* v_fvars_2749_ = stack[5].m_obj;
lean_object* v_e_2750_ = stack[6].m_obj;
lean_object* v_a_2751_ = stack[7].m_obj;
lean_object* v___y_2752_ = stack[8].m_obj;
lean_object* v___y_2753_ = stack[9].m_obj;
lean_object* v___y_2754_ = stack[10].m_obj;
lean_object* v___y_2755_ = stack[11].m_obj;
lean_object* v_res_2779_;
v_res_2779_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2744_, v_post_2745_, v_usedLetOnly_2746_, v_skipConstInApp_2747_, v_skipInstances_2748_, v_fvars_2749_, v_e_2750_, v_a_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
stack->m_obj
 = v_res_2779_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2780_, lean_object* v_pre_2781_, lean_object* v_post_2782_, uint8_t v_usedLetOnly_2783_, uint8_t v_skipConstInApp_2784_, uint8_t v_skipInstances_2785_, lean_object* v_body_2786_, lean_object* v_x_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_array_push(v_fvars_2780_, v_x_2787_);
v___x_2795_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2781_, v_post_2782_, v_usedLetOnly_2783_, v_skipConstInApp_2784_, v_skipInstances_2785_, v___x_2794_, v_body_2786_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2795_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_2780_ = stack[0].m_obj;
lean_object* v_pre_2781_ = stack[1].m_obj;
lean_object* v_post_2782_ = stack[2].m_obj;
uint8_t v_usedLetOnly_2783_ = stack[3].m_num;
uint8_t v_skipConstInApp_2784_ = stack[4].m_num;
uint8_t v_skipInstances_2785_ = stack[5].m_num;
lean_object* v_body_2786_ = stack[6].m_obj;
lean_object* v_x_2787_ = stack[7].m_obj;
lean_object* v___y_2788_ = stack[8].m_obj;
lean_object* v___y_2789_ = stack[9].m_obj;
lean_object* v___y_2790_ = stack[10].m_obj;
lean_object* v___y_2791_ = stack[11].m_obj;
lean_object* v___y_2792_ = stack[12].m_obj;
lean_object* v_res_2796_;
v_res_2796_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2780_, v_pre_2781_, v_post_2782_, v_usedLetOnly_2783_, v_skipConstInApp_2784_, v_skipInstances_2785_, v_body_2786_, v_x_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
stack->m_obj
 = v_res_2796_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2797_, lean_object* v_pre_2798_, lean_object* v_post_2799_, lean_object* v_usedLetOnly_2800_, lean_object* v_skipConstInApp_2801_, lean_object* v_skipInstances_2802_, lean_object* v_body_2803_, lean_object* v_x_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
uint8_t v_usedLetOnly_boxed_2811_; uint8_t v_skipConstInApp_boxed_2812_; uint8_t v_skipInstances_boxed_2813_; lean_object* v_res_2814_; 
v_usedLetOnly_boxed_2811_ = lean_unbox(v_usedLetOnly_2800_);
v_skipConstInApp_boxed_2812_ = lean_unbox(v_skipConstInApp_2801_);
v_skipInstances_boxed_2813_ = lean_unbox(v_skipInstances_2802_);
v_res_2814_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2797_, v_pre_2798_, v_post_2799_, v_usedLetOnly_boxed_2811_, v_skipConstInApp_boxed_2812_, v_skipInstances_boxed_2813_, v_body_2803_, v_x_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v___y_2805_);
return v_res_2814_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2815_, lean_object* v_post_2816_, uint8_t v_usedLetOnly_2817_, uint8_t v_skipConstInApp_2818_, uint8_t v_skipInstances_2819_, lean_object* v_fvars_2820_, lean_object* v_e_2821_, lean_object* v_a_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
if (lean_obj_tag(v_e_2821_) == 8)
{
lean_object* v_declName_2828_; lean_object* v_type_2829_; lean_object* v_value_2830_; lean_object* v_body_2831_; uint8_t v_nondep_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___f_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_declName_2828_ = lean_ctor_get(v_e_2821_, 0);
lean_inc(v_declName_2828_);
v_type_2829_ = lean_ctor_get(v_e_2821_, 1);
lean_inc_ref(v_type_2829_);
v_value_2830_ = lean_ctor_get(v_e_2821_, 2);
lean_inc_ref(v_value_2830_);
v_body_2831_ = lean_ctor_get(v_e_2821_, 3);
lean_inc_ref(v_body_2831_);
v_nondep_2832_ = lean_ctor_get_uint8(v_e_2821_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2821_, 4);
v___x_2833_ = lean_box(v_usedLetOnly_2817_);
v___x_2834_ = lean_box(v_skipConstInApp_2818_);
v___x_2835_ = lean_box(v_skipInstances_2819_);
lean_inc_ref_n(v_post_2816_, 2);
lean_inc_ref_n(v_pre_2815_, 2);
lean_inc_ref(v_fvars_2820_);
v___f_2836_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2836_, 0, v_fvars_2820_);
lean_closure_set(v___f_2836_, 1, v_pre_2815_);
lean_closure_set(v___f_2836_, 2, v_post_2816_);
lean_closure_set(v___f_2836_, 3, v___x_2833_);
lean_closure_set(v___f_2836_, 4, v___x_2834_);
lean_closure_set(v___f_2836_, 5, v___x_2835_);
lean_closure_set(v___f_2836_, 6, v_body_2831_);
v___x_2837_ = lean_expr_instantiate_rev(v_type_2829_, v_fvars_2820_);
lean_dec_ref(v_type_2829_);
v___x_2838_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v___x_2837_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___x_2840_ = lean_expr_instantiate_rev(v_value_2830_, v_fvars_2820_);
lean_dec_ref(v_fvars_2820_);
lean_dec_ref(v_value_2830_);
v___x_2841_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v___x_2840_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; uint8_t v___x_2843_; lean_object* v___x_2844_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v___x_2843_ = 0;
v___x_2844_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2828_, v_a_2839_, v_a_2842_, v___f_2836_, v_nondep_2832_, v___x_2843_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2844_;
}
else
{
lean_dec(v_a_2839_);
lean_dec_ref(v___f_2836_);
lean_dec(v_declName_2828_);
return v___x_2841_;
}
}
else
{
lean_dec_ref(v___f_2836_);
lean_dec_ref(v_value_2830_);
lean_dec(v_declName_2828_);
lean_dec_ref(v_fvars_2820_);
lean_dec_ref(v_post_2816_);
lean_dec_ref(v_pre_2815_);
return v___x_2838_;
}
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_expr_instantiate_rev(v_e_2821_, v_fvars_2820_);
lean_dec_ref(v_e_2821_);
lean_inc_ref(v_post_2816_);
lean_inc_ref(v_pre_2815_);
v___x_2846_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v___x_2845_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; uint8_t v___x_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v___x_2848_ = 0;
v___x_2849_ = 1;
v___x_2850_ = l_Lean_Meta_mkLetFVars(v_fvars_2820_, v_a_2847_, v_usedLetOnly_2817_, v___x_2848_, v___x_2849_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec_ref(v_fvars_2820_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; lean_object* v___x_2852_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v___x_2852_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v_a_2851_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
return v___x_2852_;
}
else
{
lean_dec_ref(v_post_2816_);
lean_dec_ref(v_pre_2815_);
return v___x_2850_;
}
}
else
{
lean_dec_ref(v_fvars_2820_);
lean_dec_ref(v_post_2816_);
lean_dec_ref(v_pre_2815_);
return v___x_2846_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2815_ = stack[0].m_obj;
lean_object* v_post_2816_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2817_ = stack[2].m_num;
uint8_t v_skipConstInApp_2818_ = stack[3].m_num;
uint8_t v_skipInstances_2819_ = stack[4].m_num;
lean_object* v_fvars_2820_ = stack[5].m_obj;
lean_object* v_e_2821_ = stack[6].m_obj;
lean_object* v_a_2822_ = stack[7].m_obj;
lean_object* v___y_2823_ = stack[8].m_obj;
lean_object* v___y_2824_ = stack[9].m_obj;
lean_object* v___y_2825_ = stack[10].m_obj;
lean_object* v___y_2826_ = stack[11].m_obj;
lean_object* v_res_2853_;
v_res_2853_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2815_, v_post_2816_, v_usedLetOnly_2817_, v_skipConstInApp_2818_, v_skipInstances_2819_, v_fvars_2820_, v_e_2821_, v_a_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
stack->m_obj
 = v_res_2853_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_pre_2854_, lean_object* v_post_2855_, uint8_t v_usedLetOnly_2856_, uint8_t v_skipConstInApp_2857_, uint8_t v_skipInstances_2858_, size_t v_sz_2859_, size_t v_i_2860_, lean_object* v_bs_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v___x_2868_; 
v___x_2868_ = lean_usize_dec_lt(v_i_2860_, v_sz_2859_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
lean_dec_ref(v_post_2855_);
lean_dec_ref(v_pre_2854_);
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v_bs_2861_);
return v___x_2869_;
}
else
{
lean_object* v_v_2870_; lean_object* v___x_2871_; lean_object* v_bs_x27_2872_; lean_object* v___x_2873_; 
v_v_2870_ = lean_array_uget(v_bs_2861_, v_i_2860_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v_bs_x27_2872_ = lean_array_uset(v_bs_2861_, v_i_2860_, v___x_2871_);
lean_inc_ref(v_post_2855_);
lean_inc_ref(v_pre_2854_);
v___x_2873_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2854_, v_post_2855_, v_usedLetOnly_2856_, v_skipConstInApp_2857_, v_skipInstances_2858_, v_v_2870_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; size_t v___x_2875_; size_t v___x_2876_; lean_object* v___x_2877_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = ((size_t)1ULL);
v___x_2876_ = lean_usize_add(v_i_2860_, v___x_2875_);
v___x_2877_ = lean_array_uset(v_bs_x27_2872_, v_i_2860_, v_a_2874_);
v_i_2860_ = v___x_2876_;
v_bs_2861_ = v___x_2877_;
goto _start;
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec_ref(v_bs_x27_2872_);
lean_dec_ref(v_post_2855_);
lean_dec_ref(v_pre_2854_);
v_a_2879_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2873_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2873_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2854_ = stack[0].m_obj;
lean_object* v_post_2855_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2856_ = stack[2].m_num;
uint8_t v_skipConstInApp_2857_ = stack[3].m_num;
uint8_t v_skipInstances_2858_ = stack[4].m_num;
size_t v_sz_2859_ = stack[5].m_num;
size_t v_i_2860_ = stack[6].m_num;
lean_object* v_bs_2861_ = stack[7].m_obj;
lean_object* v___y_2862_ = stack[8].m_obj;
lean_object* v___y_2863_ = stack[9].m_obj;
lean_object* v___y_2864_ = stack[10].m_obj;
lean_object* v___y_2865_ = stack[11].m_obj;
lean_object* v___y_2866_ = stack[12].m_obj;
lean_object* v_res_2887_;
v_res_2887_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2854_, v_post_2855_, v_usedLetOnly_2856_, v_skipConstInApp_2857_, v_skipInstances_2858_, v_sz_2859_, v_i_2860_, v_bs_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
stack->m_obj
 = v_res_2887_;
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_2888_, lean_object* v_post_2889_, uint8_t v_usedLetOnly_2890_, uint8_t v_skipConstInApp_2891_, uint8_t v_skipInstances_2892_, lean_object* v___x_2893_, lean_object* v___y_2894_, lean_object* v_b_2895_, lean_object* v_a_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2888_, v_post_2889_, v_usedLetOnly_2890_, v_skipConstInApp_2891_, v_skipInstances_2892_, v___x_2893_, v___y_2894_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2912_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2912_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2912_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2907_ = lean_array_fset(v_b_2895_, v_a_2896_, v_a_2903_);
v___x_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2907_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2908_);
v___x_2910_ = v___x_2905_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_b_2895_);
v_a_2913_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2902_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2902_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_2888_ = stack[0].m_obj;
lean_object* v_post_2889_ = stack[1].m_obj;
uint8_t v_usedLetOnly_2890_ = stack[2].m_num;
uint8_t v_skipConstInApp_2891_ = stack[3].m_num;
uint8_t v_skipInstances_2892_ = stack[4].m_num;
lean_object* v___x_2893_ = stack[5].m_obj;
lean_object* v___y_2894_ = stack[6].m_obj;
lean_object* v_b_2895_ = stack[7].m_obj;
lean_object* v_a_2896_ = stack[8].m_obj;
lean_object* v___y_2897_ = stack[9].m_obj;
lean_object* v___y_2898_ = stack[10].m_obj;
lean_object* v___y_2899_ = stack[11].m_obj;
lean_object* v___y_2900_ = stack[12].m_obj;
lean_object* v_res_2921_;
v_res_2921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2888_, v_post_2889_, v_usedLetOnly_2890_, v_skipConstInApp_2891_, v_skipInstances_2892_, v___x_2893_, v___y_2894_, v_b_2895_, v_a_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
stack->m_obj
 = v_res_2921_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_2922_, lean_object* v_post_2923_, lean_object* v_usedLetOnly_2924_, lean_object* v_skipConstInApp_2925_, lean_object* v_skipInstances_2926_, lean_object* v___x_2927_, lean_object* v___y_2928_, lean_object* v_b_2929_, lean_object* v_a_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v_usedLetOnly_boxed_2936_; uint8_t v_skipConstInApp_boxed_2937_; uint8_t v_skipInstances_boxed_2938_; lean_object* v_res_2939_; 
v_usedLetOnly_boxed_2936_ = lean_unbox(v_usedLetOnly_2924_);
v_skipConstInApp_boxed_2937_ = lean_unbox(v_skipConstInApp_2925_);
v_skipInstances_boxed_2938_ = lean_unbox(v_skipInstances_2926_);
v_res_2939_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2922_, v_post_2923_, v_usedLetOnly_boxed_2936_, v_skipConstInApp_boxed_2937_, v_skipInstances_boxed_2938_, v___x_2927_, v___y_2928_, v_b_2929_, v_a_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v_a_2930_);
lean_dec(v___y_2928_);
return v_res_2939_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object* v_upperBound_2940_, lean_object* v___x_2941_, lean_object* v_pre_2942_, lean_object* v_post_2943_, uint8_t v_usedLetOnly_2944_, uint8_t v_skipConstInApp_2945_, uint8_t v_skipInstances_2946_, lean_object* v_a_2947_, lean_object* v_b_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___y_2956_; uint8_t v___x_2979_; 
v___x_2979_ = lean_nat_dec_lt(v_a_2947_, v_upperBound_2940_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; 
lean_dec(v_a_2947_);
lean_dec_ref(v_post_2943_);
lean_dec_ref(v_pre_2942_);
v___x_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2980_, 0, v_b_2948_);
return v___x_2980_;
}
else
{
lean_object* v___x_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2981_ = lean_array_fget_borrowed(v_b_2948_, v_a_2947_);
v___x_2982_ = lean_array_get_size(v___x_2941_);
v___x_2983_ = lean_nat_dec_lt(v_a_2947_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___f_2987_; 
lean_inc(v___x_2981_);
v___x_2984_ = lean_box(v_usedLetOnly_2944_);
v___x_2985_ = lean_box(v_skipConstInApp_2945_);
v___x_2986_ = lean_box(v_skipInstances_2946_);
lean_inc(v_a_2947_);
lean_inc(v___y_2949_);
lean_inc_ref(v_post_2943_);
lean_inc_ref(v_pre_2942_);
v___f_2987_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2987_, 0, v_pre_2942_);
lean_closure_set(v___f_2987_, 1, v_post_2943_);
lean_closure_set(v___f_2987_, 2, v___x_2984_);
lean_closure_set(v___f_2987_, 3, v___x_2985_);
lean_closure_set(v___f_2987_, 4, v___x_2986_);
lean_closure_set(v___f_2987_, 5, v___x_2981_);
lean_closure_set(v___f_2987_, 6, v___y_2949_);
lean_closure_set(v___f_2987_, 7, v_b_2948_);
lean_closure_set(v___f_2987_, 8, v_a_2947_);
v___y_2956_ = v___f_2987_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2988_; uint8_t v_isInstance_2989_; 
v___x_2988_ = lean_array_fget_borrowed(v___x_2941_, v_a_2947_);
v_isInstance_2989_ = lean_ctor_get_uint8(v___x_2988_, sizeof(void*)*1 + 4);
if (v_isInstance_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___f_2993_; 
lean_inc(v___x_2981_);
v___x_2990_ = lean_box(v_usedLetOnly_2944_);
v___x_2991_ = lean_box(v_skipConstInApp_2945_);
v___x_2992_ = lean_box(v_skipInstances_2946_);
lean_inc(v_a_2947_);
lean_inc(v___y_2949_);
lean_inc_ref(v_post_2943_);
lean_inc_ref(v_pre_2942_);
v___f_2993_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2993_, 0, v_pre_2942_);
lean_closure_set(v___f_2993_, 1, v_post_2943_);
lean_closure_set(v___f_2993_, 2, v___x_2990_);
lean_closure_set(v___f_2993_, 3, v___x_2991_);
lean_closure_set(v___f_2993_, 4, v___x_2992_);
lean_closure_set(v___f_2993_, 5, v___x_2981_);
lean_closure_set(v___f_2993_, 6, v___y_2949_);
lean_closure_set(v___f_2993_, 7, v_b_2948_);
lean_closure_set(v___f_2993_, 8, v_a_2947_);
v___y_2956_ = v___f_2993_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2994_; lean_object* v___f_2995_; 
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v_b_2948_);
v___f_2995_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2995_, 0, v___x_2994_);
v___y_2956_ = v___f_2995_;
goto v___jp_2955_;
}
}
}
v___jp_2955_:
{
lean_object* v___x_2957_; 
lean_inc(v___y_2953_);
lean_inc_ref(v___y_2952_);
lean_inc(v___y_2951_);
lean_inc_ref(v___y_2950_);
v___x_2957_ = lean_apply_5(v___y_2956_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, lean_box(0));
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2970_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2970_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2970_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
if (lean_obj_tag(v_a_2958_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2964_; 
lean_dec(v_a_2947_);
lean_dec_ref(v_post_2943_);
lean_dec_ref(v_pre_2942_);
v_a_2962_ = lean_ctor_get(v_a_2958_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v_a_2958_, 1);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v_a_2962_);
v___x_2964_ = v___x_2960_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2962_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_del_object(v___x_2960_);
v_a_2966_ = lean_ctor_get(v_a_2958_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v_a_2958_, 1);
v___x_2967_ = lean_unsigned_to_nat(1u);
v___x_2968_ = lean_nat_add(v_a_2947_, v___x_2967_);
lean_dec(v_a_2947_);
v_a_2947_ = v___x_2968_;
v_b_2948_ = v_a_2966_;
goto _start;
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec(v_a_2947_);
lean_dec_ref(v_post_2943_);
lean_dec_ref(v_pre_2942_);
v_a_2971_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2957_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2957_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_2940_ = stack[0].m_obj;
lean_object* v___x_2941_ = stack[1].m_obj;
lean_object* v_pre_2942_ = stack[2].m_obj;
lean_object* v_post_2943_ = stack[3].m_obj;
uint8_t v_usedLetOnly_2944_ = stack[4].m_num;
uint8_t v_skipConstInApp_2945_ = stack[5].m_num;
uint8_t v_skipInstances_2946_ = stack[6].m_num;
lean_object* v_a_2947_ = stack[7].m_obj;
lean_object* v_b_2948_ = stack[8].m_obj;
lean_object* v___y_2949_ = stack[9].m_obj;
lean_object* v___y_2950_ = stack[10].m_obj;
lean_object* v___y_2951_ = stack[11].m_obj;
lean_object* v___y_2952_ = stack[12].m_obj;
lean_object* v___y_2953_ = stack[13].m_obj;
lean_object* v_res_2996_;
v_res_2996_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_2940_, v___x_2941_, v_pre_2942_, v_post_2943_, v_usedLetOnly_2944_, v_skipConstInApp_2945_, v_skipInstances_2946_, v_a_2947_, v_b_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
stack->m_obj
 = v_res_2996_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2997_, lean_object* v_pre_2998_, lean_object* v_post_2999_, uint8_t v_usedLetOnly_3000_, uint8_t v_skipConstInApp_3001_, lean_object* v_x_3002_, lean_object* v_x_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_f_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; 
if (lean_obj_tag(v_x_3002_) == 5)
{
lean_object* v_fn_3060_; lean_object* v_arg_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v_fn_3060_ = lean_ctor_get(v_x_3002_, 0);
lean_inc_ref(v_fn_3060_);
v_arg_3061_ = lean_ctor_get(v_x_3002_, 1);
lean_inc_ref(v_arg_3061_);
lean_dec_ref_known(v_x_3002_, 2);
v___x_3062_ = lean_array_set(v_x_3003_, v_x_3004_, v_arg_3061_);
v___x_3063_ = lean_unsigned_to_nat(1u);
v___x_3064_ = lean_nat_sub(v_x_3004_, v___x_3063_);
lean_dec(v_x_3004_);
v_x_3002_ = v_fn_3060_;
v_x_3003_ = v___x_3062_;
v_x_3004_ = v___x_3064_;
goto _start;
}
else
{
lean_dec(v_x_3004_);
if (v_skipConstInApp_3001_ == 0)
{
goto v___jp_3057_;
}
else
{
uint8_t v___x_3066_; 
v___x_3066_ = l_Lean_Expr_isConst(v_x_3002_);
if (v___x_3066_ == 0)
{
goto v___jp_3057_;
}
else
{
v_f_3012_ = v_x_3002_;
v___y_3013_ = v___y_3005_;
v___y_3014_ = v___y_3006_;
v___y_3015_ = v___y_3007_;
v___y_3016_ = v___y_3008_;
v___y_3017_ = v___y_3009_;
goto v___jp_3011_;
}
}
}
v___jp_3011_:
{
if (v_skipInstances_2997_ == 0)
{
size_t v_sz_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
v_sz_3018_ = lean_array_size(v_x_3003_);
v___x_3019_ = ((size_t)0ULL);
lean_inc_ref(v_post_2999_);
lean_inc_ref(v_pre_2998_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2998_, v_post_2999_, v_usedLetOnly_3000_, v_skipConstInApp_3001_, v_skipInstances_2997_, v_sz_3018_, v___x_3019_, v_x_3003_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = l_Lean_mkAppN(v_f_3012_, v_a_3021_);
lean_dec(v_a_3021_);
v___x_3023_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2998_, v_post_2999_, v_usedLetOnly_3000_, v_skipConstInApp_3001_, v_skipInstances_2997_, v___x_3022_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3023_;
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec_ref(v_f_3012_);
lean_dec_ref(v_post_2999_);
lean_dec_ref(v_pre_2998_);
v_a_3024_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_3020_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3020_);
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
v___x_3032_ = lean_array_get_size(v_x_3003_);
lean_inc_ref(v_f_3012_);
v___x_3033_ = l_Lean_Meta_getFunInfoNArgs(v_f_3012_, v___x_3032_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v_paramInfo_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v_paramInfo_3035_ = lean_ctor_get(v_a_3034_, 0);
lean_inc_ref(v_paramInfo_3035_);
lean_dec(v_a_3034_);
v___x_3036_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2999_);
lean_inc_ref(v_pre_2998_);
v___x_3037_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v___x_3032_, v_paramInfo_3035_, v_pre_2998_, v_post_2999_, v_usedLetOnly_3000_, v_skipConstInApp_3001_, v_skipInstances_2997_, v___x_3036_, v_x_3003_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
lean_dec_ref(v_paramInfo_3035_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3039_ = l_Lean_mkAppN(v_f_3012_, v_a_3038_);
lean_dec(v_a_3038_);
v___x_3040_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2998_, v_post_2999_, v_usedLetOnly_3000_, v_skipConstInApp_3001_, v_skipInstances_2997_, v___x_3039_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
return v___x_3040_;
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v_f_3012_);
lean_dec_ref(v_post_2999_);
lean_dec_ref(v_pre_2998_);
v_a_3041_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_3037_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_3037_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v_f_3012_);
lean_dec_ref(v_x_3003_);
lean_dec_ref(v_post_2999_);
lean_dec_ref(v_pre_2998_);
v_a_3049_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3033_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3033_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
v___jp_3057_:
{
lean_object* v___x_3058_; 
lean_inc_ref(v_post_2999_);
lean_inc_ref(v_pre_2998_);
v___x_3058_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2998_, v_post_2999_, v_usedLetOnly_3000_, v_skipConstInApp_3001_, v_skipInstances_2997_, v_x_3002_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
v_f_3012_ = v_a_3059_;
v___y_3013_ = v___y_3005_;
v___y_3014_ = v___y_3006_;
v___y_3015_ = v___y_3007_;
v___y_3016_ = v___y_3008_;
v___y_3017_ = v___y_3009_;
goto v___jp_3011_;
}
else
{
lean_dec_ref(v_x_3003_);
lean_dec_ref(v_post_2999_);
lean_dec_ref(v_pre_2998_);
return v___x_3058_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11_0interp(lean_interpreter_value* stack)
{
uint8_t v_skipInstances_2997_ = stack[0].m_num;
lean_object* v_pre_2998_ = stack[1].m_obj;
lean_object* v_post_2999_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3000_ = stack[3].m_num;
uint8_t v_skipConstInApp_3001_ = stack[4].m_num;
lean_object* v_x_3002_ = stack[5].m_obj;
lean_object* v_x_3003_ = stack[6].m_obj;
lean_object* v_x_3004_ = stack[7].m_obj;
lean_object* v___y_3005_ = stack[8].m_obj;
lean_object* v___y_3006_ = stack[9].m_obj;
lean_object* v___y_3007_ = stack[10].m_obj;
lean_object* v___y_3008_ = stack[11].m_obj;
lean_object* v___y_3009_ = stack[12].m_obj;
lean_object* v_res_3067_;
v_res_3067_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_2997_, v_pre_2998_, v_post_2999_, v_usedLetOnly_3000_, v_skipConstInApp_3001_, v_x_3002_, v_x_3003_, v_x_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
stack->m_obj
 = v_res_3067_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v___x_3068_, lean_object* v_pre_3069_, lean_object* v_e_3070_, lean_object* v_post_3071_, uint8_t v_usedLetOnly_3072_, uint8_t v_skipConstInApp_3073_, uint8_t v_skipInstances_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_Core_checkSystem(v___x_3068_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v___x_3082_; 
lean_dec_ref_known(v___x_3081_, 1);
lean_inc_ref(v_pre_3069_);
lean_inc(v___y_3079_);
lean_inc_ref(v___y_3078_);
lean_inc(v___y_3077_);
lean_inc_ref(v___y_3076_);
lean_inc_ref(v_e_3070_);
v___x_3082_ = lean_apply_6(v_pre_3069_, v_e_3070_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, lean_box(0));
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3131_; 
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3131_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3131_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___y_3088_; 
switch(lean_obj_tag(v_a_3083_))
{
case 0:
{
lean_object* v_e_3123_; lean_object* v___x_3125_; 
lean_dec_ref(v_post_3071_);
lean_dec_ref(v_e_3070_);
lean_dec_ref(v_pre_3069_);
v_e_3123_ = lean_ctor_get(v_a_3083_, 0);
lean_inc_ref(v_e_3123_);
lean_dec_ref_known(v_a_3083_, 1);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v_e_3123_);
v___x_3125_ = v___x_3085_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_e_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
case 1:
{
lean_object* v_e_3127_; lean_object* v___x_3128_; 
lean_del_object(v___x_3085_);
lean_dec_ref(v_e_3070_);
v_e_3127_ = lean_ctor_get(v_a_3083_, 0);
lean_inc_ref(v_e_3127_);
lean_dec_ref_known(v_a_3083_, 1);
v___x_3128_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v_e_3127_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3128_;
}
default: 
{
lean_object* v_e_x3f_3129_; 
lean_del_object(v___x_3085_);
v_e_x3f_3129_ = lean_ctor_get(v_a_3083_, 0);
lean_inc(v_e_x3f_3129_);
lean_dec_ref_known(v_a_3083_, 1);
if (lean_obj_tag(v_e_x3f_3129_) == 0)
{
v___y_3088_ = v_e_3070_;
goto v___jp_3087_;
}
else
{
lean_object* v_val_3130_; 
lean_dec_ref(v_e_3070_);
v_val_3130_ = lean_ctor_get(v_e_x3f_3129_, 0);
lean_inc(v_val_3130_);
lean_dec_ref_known(v_e_x3f_3129_, 1);
v___y_3088_ = v_val_3130_;
goto v___jp_3087_;
}
}
}
v___jp_3087_:
{
switch(lean_obj_tag(v___y_3088_))
{
case 7:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3090_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___x_3089_, v___y_3088_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3090_;
}
case 6:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3092_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___x_3091_, v___y_3088_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3092_;
}
case 8:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3094_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___x_3093_, v___y_3088_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3094_;
}
case 5:
{
lean_object* v_dummy_3095_; lean_object* v_nargs_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v_dummy_3095_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3096_ = l_Lean_Expr_getAppNumArgs(v___y_3088_);
lean_inc(v_nargs_3096_);
v___x_3097_ = lean_mk_array(v_nargs_3096_, v_dummy_3095_);
v___x_3098_ = lean_unsigned_to_nat(1u);
v___x_3099_ = lean_nat_sub(v_nargs_3096_, v___x_3098_);
lean_dec(v_nargs_3096_);
v___x_3100_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_3074_, v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v___y_3088_, v___x_3097_, v___x_3099_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3100_;
}
case 10:
{
lean_object* v_data_3101_; lean_object* v_expr_3102_; lean_object* v___x_3103_; 
v_data_3101_ = lean_ctor_get(v___y_3088_, 0);
v_expr_3102_ = lean_ctor_get(v___y_3088_, 1);
lean_inc_ref(v_expr_3102_);
lean_inc_ref(v_post_3071_);
lean_inc_ref(v_pre_3069_);
v___x_3103_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v_expr_3102_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; size_t v___x_3105_; size_t v___x_3106_; uint8_t v___x_3107_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = lean_ptr_addr(v_expr_3102_);
v___x_3106_ = lean_ptr_addr(v_a_3104_);
v___x_3107_ = lean_usize_dec_eq(v___x_3105_, v___x_3106_);
if (v___x_3107_ == 0)
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_inc(v_data_3101_);
lean_dec_ref_known(v___y_3088_, 2);
v___x_3108_ = l_Lean_Expr_mdata___override(v_data_3101_, v_a_3104_);
v___x_3109_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___x_3108_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3109_;
}
else
{
lean_object* v___x_3110_; 
lean_dec(v_a_3104_);
v___x_3110_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___y_3088_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3110_;
}
}
else
{
lean_dec_ref_known(v___y_3088_, 2);
lean_dec_ref(v_post_3071_);
lean_dec_ref(v_pre_3069_);
return v___x_3103_;
}
}
case 11:
{
lean_object* v_typeName_3111_; lean_object* v_idx_3112_; lean_object* v_struct_3113_; lean_object* v___x_3114_; 
v_typeName_3111_ = lean_ctor_get(v___y_3088_, 0);
v_idx_3112_ = lean_ctor_get(v___y_3088_, 1);
v_struct_3113_ = lean_ctor_get(v___y_3088_, 2);
lean_inc_ref(v_struct_3113_);
lean_inc_ref(v_post_3071_);
lean_inc_ref(v_pre_3069_);
v___x_3114_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v_struct_3113_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; size_t v___x_3116_; size_t v___x_3117_; uint8_t v___x_3118_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = lean_ptr_addr(v_struct_3113_);
v___x_3117_ = lean_ptr_addr(v_a_3115_);
v___x_3118_ = lean_usize_dec_eq(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_inc(v_idx_3112_);
lean_inc(v_typeName_3111_);
lean_dec_ref_known(v___y_3088_, 3);
v___x_3119_ = l_Lean_Expr_proj___override(v_typeName_3111_, v_idx_3112_, v_a_3115_);
v___x_3120_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___x_3119_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3120_;
}
else
{
lean_object* v___x_3121_; 
lean_dec(v_a_3115_);
v___x_3121_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___y_3088_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3121_;
}
}
else
{
lean_dec_ref_known(v___y_3088_, 3);
lean_dec_ref(v_post_3071_);
lean_dec_ref(v_pre_3069_);
return v___x_3114_;
}
}
default: 
{
lean_object* v___x_3122_; 
v___x_3122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3069_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___y_3088_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3122_;
}
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v_post_3071_);
lean_dec_ref(v_e_3070_);
lean_dec_ref(v_pre_3069_);
v_a_3132_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3082_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3082_);
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
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v_post_3071_);
lean_dec_ref(v_e_3070_);
lean_dec_ref(v_pre_3069_);
v_a_3140_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3081_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3081_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3068_ = stack[0].m_obj;
lean_object* v_pre_3069_ = stack[1].m_obj;
lean_object* v_e_3070_ = stack[2].m_obj;
lean_object* v_post_3071_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3072_ = stack[4].m_num;
uint8_t v_skipConstInApp_3073_ = stack[5].m_num;
uint8_t v_skipInstances_3074_ = stack[6].m_num;
lean_object* v___y_3075_ = stack[7].m_obj;
lean_object* v___y_3076_ = stack[8].m_obj;
lean_object* v___y_3077_ = stack[9].m_obj;
lean_object* v___y_3078_ = stack[10].m_obj;
lean_object* v___y_3079_ = stack[11].m_obj;
lean_object* v_res_3148_;
v_res_3148_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v___x_3068_, v_pre_3069_, v_e_3070_, v_post_3071_, v_usedLetOnly_3072_, v_skipConstInApp_3073_, v_skipInstances_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
stack->m_obj
 = v_res_3148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v___x_3149_, lean_object* v_pre_3150_, lean_object* v_e_3151_, lean_object* v_post_3152_, lean_object* v_usedLetOnly_3153_, lean_object* v_skipConstInApp_3154_, lean_object* v_skipInstances_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v_usedLetOnly_boxed_3162_; uint8_t v_skipConstInApp_boxed_3163_; uint8_t v_skipInstances_boxed_3164_; lean_object* v_res_3165_; 
v_usedLetOnly_boxed_3162_ = lean_unbox(v_usedLetOnly_3153_);
v_skipConstInApp_boxed_3163_ = lean_unbox(v_skipConstInApp_3154_);
v_skipInstances_boxed_3164_ = lean_unbox(v_skipInstances_3155_);
v_res_3165_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v___x_3149_, v_pre_3150_, v_e_3151_, v_post_3152_, v_usedLetOnly_boxed_3162_, v_skipConstInApp_boxed_3163_, v_skipInstances_boxed_3164_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
return v_res_3165_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3166_, lean_object* v_post_3167_, uint8_t v_usedLetOnly_3168_, uint8_t v_skipConstInApp_3169_, uint8_t v_skipInstances_3170_, lean_object* v_e_3171_, lean_object* v_a_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_inc(v_a_3172_);
v___x_3178_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3178_, 0, lean_box(0));
lean_closure_set(v___x_3178_, 1, lean_box(0));
lean_closure_set(v___x_3178_, 2, v_a_3172_);
v___x_3179_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3178_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3214_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3182_ = v___x_3179_;
v_isShared_3183_ = v_isSharedCheck_3214_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3179_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3214_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3180_, v_e_3171_);
lean_dec(v_a_3180_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___f_3189_; lean_object* v___x_3190_; 
lean_del_object(v___x_3182_);
v___x_3185_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
v___x_3186_ = lean_box(v_usedLetOnly_3168_);
v___x_3187_ = lean_box(v_skipConstInApp_3169_);
v___x_3188_ = lean_box(v_skipInstances_3170_);
lean_inc_ref(v_e_3171_);
v___f_3189_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3189_, 0, v___x_3185_);
lean_closure_set(v___f_3189_, 1, v_pre_3166_);
lean_closure_set(v___f_3189_, 2, v_e_3171_);
lean_closure_set(v___f_3189_, 3, v_post_3167_);
lean_closure_set(v___f_3189_, 4, v___x_3186_);
lean_closure_set(v___f_3189_, 5, v___x_3187_);
lean_closure_set(v___f_3189_, 6, v___x_3188_);
v___x_3190_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3189_, v_a_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___f_3192_; lean_object* v___x_3193_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc_n(v_a_3191_, 2);
lean_dec_ref_known(v___x_3190_, 1);
lean_inc(v_a_3172_);
v___f_3192_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3192_, 0, v_a_3172_);
lean_closure_set(v___f_3192_, 1, v_e_3171_);
lean_closure_set(v___f_3192_, 2, v_a_3191_);
v___x_3193_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3192_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v___x_3193_, 0);
lean_dec(v_unused_3201_);
v___x_3195_ = v___x_3193_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_dec(v___x_3193_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_a_3191_);
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3191_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec(v_a_3191_);
v_a_3202_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3193_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3193_);
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
else
{
lean_dec_ref(v_e_3171_);
return v___x_3190_;
}
}
else
{
lean_object* v_val_3210_; lean_object* v___x_3212_; 
lean_dec_ref(v_e_3171_);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3166_);
v_val_3210_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_val_3210_);
lean_dec_ref_known(v___x_3184_, 1);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v_val_3210_);
v___x_3212_ = v___x_3182_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_val_3210_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref(v_e_3171_);
lean_dec_ref(v_post_3167_);
lean_dec_ref(v_pre_3166_);
v_a_3215_ = lean_ctor_get(v___x_3179_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3179_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3179_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3166_ = stack[0].m_obj;
lean_object* v_post_3167_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3168_ = stack[2].m_num;
uint8_t v_skipConstInApp_3169_ = stack[3].m_num;
uint8_t v_skipInstances_3170_ = stack[4].m_num;
lean_object* v_e_3171_ = stack[5].m_obj;
lean_object* v_a_3172_ = stack[6].m_obj;
lean_object* v___y_3173_ = stack[7].m_obj;
lean_object* v___y_3174_ = stack[8].m_obj;
lean_object* v___y_3175_ = stack[9].m_obj;
lean_object* v___y_3176_ = stack[10].m_obj;
lean_object* v_res_3223_;
v_res_3223_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3166_, v_post_3167_, v_usedLetOnly_3168_, v_skipConstInApp_3169_, v_skipInstances_3170_, v_e_3171_, v_a_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
stack->m_obj
 = v_res_3223_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3224_, lean_object* v_post_3225_, uint8_t v_usedLetOnly_3226_, uint8_t v_skipConstInApp_3227_, uint8_t v_skipInstances_3228_, lean_object* v_fvars_3229_, lean_object* v_e_3230_, lean_object* v_a_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
if (lean_obj_tag(v_e_3230_) == 7)
{
lean_object* v_binderName_3237_; lean_object* v_binderType_3238_; lean_object* v_body_3239_; uint8_t v_binderInfo_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v_binderName_3237_ = lean_ctor_get(v_e_3230_, 0);
lean_inc(v_binderName_3237_);
v_binderType_3238_ = lean_ctor_get(v_e_3230_, 1);
lean_inc_ref(v_binderType_3238_);
v_body_3239_ = lean_ctor_get(v_e_3230_, 2);
lean_inc_ref(v_body_3239_);
v_binderInfo_3240_ = lean_ctor_get_uint8(v_e_3230_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3230_, 3);
v___x_3241_ = lean_box(v_usedLetOnly_3226_);
v___x_3242_ = lean_box(v_skipConstInApp_3227_);
v___x_3243_ = lean_box(v_skipInstances_3228_);
lean_inc_ref(v_post_3225_);
lean_inc_ref(v_pre_3224_);
lean_inc_ref(v_fvars_3229_);
v___f_3244_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3244_, 0, v_fvars_3229_);
lean_closure_set(v___f_3244_, 1, v_pre_3224_);
lean_closure_set(v___f_3244_, 2, v_post_3225_);
lean_closure_set(v___f_3244_, 3, v___x_3241_);
lean_closure_set(v___f_3244_, 4, v___x_3242_);
lean_closure_set(v___f_3244_, 5, v___x_3243_);
lean_closure_set(v___f_3244_, 6, v_body_3239_);
v___x_3245_ = lean_expr_instantiate_rev(v_binderType_3238_, v_fvars_3229_);
lean_dec_ref(v_fvars_3229_);
lean_dec_ref(v_binderType_3238_);
v___x_3246_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3224_, v_post_3225_, v_usedLetOnly_3226_, v_skipConstInApp_3227_, v_skipInstances_3228_, v___x_3245_, v_a_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; uint8_t v___x_3248_; lean_object* v___x_3249_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref_known(v___x_3246_, 1);
v___x_3248_ = 0;
v___x_3249_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3237_, v_binderInfo_3240_, v_a_3247_, v___f_3244_, v___x_3248_, v_a_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3249_;
}
else
{
lean_dec_ref(v___f_3244_);
lean_dec(v_binderName_3237_);
return v___x_3246_;
}
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = lean_expr_instantiate_rev(v_e_3230_, v_fvars_3229_);
lean_dec_ref(v_e_3230_);
lean_inc_ref(v_post_3225_);
lean_inc_ref(v_pre_3224_);
v___x_3251_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3224_, v_post_3225_, v_usedLetOnly_3226_, v_skipConstInApp_3227_, v_skipInstances_3228_, v___x_3250_, v_a_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; uint8_t v___x_3253_; uint8_t v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref_known(v___x_3251_, 1);
v___x_3253_ = 0;
v___x_3254_ = 1;
v___x_3255_ = 1;
v___x_3256_ = l_Lean_Meta_mkForallFVars(v_fvars_3229_, v_a_3252_, v___x_3253_, v_usedLetOnly_3226_, v___x_3254_, v___x_3255_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
lean_dec_ref(v_fvars_3229_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_object* v_a_3257_; lean_object* v___x_3258_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
lean_dec_ref_known(v___x_3256_, 1);
v___x_3258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3224_, v_post_3225_, v_usedLetOnly_3226_, v_skipConstInApp_3227_, v_skipInstances_3228_, v_a_3257_, v_a_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3258_;
}
else
{
lean_dec_ref(v_post_3225_);
lean_dec_ref(v_pre_3224_);
return v___x_3256_;
}
}
else
{
lean_dec_ref(v_fvars_3229_);
lean_dec_ref(v_post_3225_);
lean_dec_ref(v_pre_3224_);
return v___x_3251_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3224_ = stack[0].m_obj;
lean_object* v_post_3225_ = stack[1].m_obj;
uint8_t v_usedLetOnly_3226_ = stack[2].m_num;
uint8_t v_skipConstInApp_3227_ = stack[3].m_num;
uint8_t v_skipInstances_3228_ = stack[4].m_num;
lean_object* v_fvars_3229_ = stack[5].m_obj;
lean_object* v_e_3230_ = stack[6].m_obj;
lean_object* v_a_3231_ = stack[7].m_obj;
lean_object* v___y_3232_ = stack[8].m_obj;
lean_object* v___y_3233_ = stack[9].m_obj;
lean_object* v___y_3234_ = stack[10].m_obj;
lean_object* v___y_3235_ = stack[11].m_obj;
lean_object* v_res_3259_;
v_res_3259_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3224_, v_post_3225_, v_usedLetOnly_3226_, v_skipConstInApp_3227_, v_skipInstances_3228_, v_fvars_3229_, v_e_3230_, v_a_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
stack->m_obj
 = v_res_3259_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3260_, lean_object* v_pre_3261_, lean_object* v_post_3262_, uint8_t v_usedLetOnly_3263_, uint8_t v_skipConstInApp_3264_, uint8_t v_skipInstances_3265_, lean_object* v_body_3266_, lean_object* v_x_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = lean_array_push(v_fvars_3260_, v_x_3267_);
v___x_3275_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3261_, v_post_3262_, v_usedLetOnly_3263_, v_skipConstInApp_3264_, v_skipInstances_3265_, v___x_3274_, v_body_3266_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
return v___x_3275_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_3260_ = stack[0].m_obj;
lean_object* v_pre_3261_ = stack[1].m_obj;
lean_object* v_post_3262_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3263_ = stack[3].m_num;
uint8_t v_skipConstInApp_3264_ = stack[4].m_num;
uint8_t v_skipInstances_3265_ = stack[5].m_num;
lean_object* v_body_3266_ = stack[6].m_obj;
lean_object* v_x_3267_ = stack[7].m_obj;
lean_object* v___y_3268_ = stack[8].m_obj;
lean_object* v___y_3269_ = stack[9].m_obj;
lean_object* v___y_3270_ = stack[10].m_obj;
lean_object* v___y_3271_ = stack[11].m_obj;
lean_object* v___y_3272_ = stack[12].m_obj;
lean_object* v_res_3276_;
v_res_3276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_3260_, v_pre_3261_, v_post_3262_, v_usedLetOnly_3263_, v_skipConstInApp_3264_, v_skipInstances_3265_, v_body_3266_, v_x_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
stack->m_obj
 = v_res_3276_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3277_, lean_object* v_post_3278_, lean_object* v_usedLetOnly_3279_, lean_object* v_skipConstInApp_3280_, lean_object* v_skipInstances_3281_, lean_object* v_e_3282_, lean_object* v_a_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
uint8_t v_usedLetOnly_boxed_3289_; uint8_t v_skipConstInApp_boxed_3290_; uint8_t v_skipInstances_boxed_3291_; lean_object* v_res_3292_; 
v_usedLetOnly_boxed_3289_ = lean_unbox(v_usedLetOnly_3279_);
v_skipConstInApp_boxed_3290_ = lean_unbox(v_skipConstInApp_3280_);
v_skipInstances_boxed_3291_ = lean_unbox(v_skipInstances_3281_);
v_res_3292_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3277_, v_post_3278_, v_usedLetOnly_boxed_3289_, v_skipConstInApp_boxed_3290_, v_skipInstances_boxed_3291_, v_e_3282_, v_a_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v_a_3283_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_pre_3293_, lean_object* v_post_3294_, lean_object* v_usedLetOnly_3295_, lean_object* v_skipConstInApp_3296_, lean_object* v_skipInstances_3297_, lean_object* v_sz_3298_, lean_object* v_i_3299_, lean_object* v_bs_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
uint8_t v_usedLetOnly_boxed_3307_; uint8_t v_skipConstInApp_boxed_3308_; uint8_t v_skipInstances_boxed_3309_; size_t v_sz_boxed_3310_; size_t v_i_boxed_3311_; lean_object* v_res_3312_; 
v_usedLetOnly_boxed_3307_ = lean_unbox(v_usedLetOnly_3295_);
v_skipConstInApp_boxed_3308_ = lean_unbox(v_skipConstInApp_3296_);
v_skipInstances_boxed_3309_ = lean_unbox(v_skipInstances_3297_);
v_sz_boxed_3310_ = lean_unbox_usize(v_sz_3298_);
lean_dec(v_sz_3298_);
v_i_boxed_3311_ = lean_unbox_usize(v_i_3299_);
lean_dec(v_i_3299_);
v_res_3312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_3293_, v_post_3294_, v_usedLetOnly_boxed_3307_, v_skipConstInApp_boxed_3308_, v_skipInstances_boxed_3309_, v_sz_boxed_3310_, v_i_boxed_3311_, v_bs_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v___y_3301_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3313_, lean_object* v_post_3314_, lean_object* v_usedLetOnly_3315_, lean_object* v_skipConstInApp_3316_, lean_object* v_skipInstances_3317_, lean_object* v_e_3318_, lean_object* v_a_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
uint8_t v_usedLetOnly_boxed_3325_; uint8_t v_skipConstInApp_boxed_3326_; uint8_t v_skipInstances_boxed_3327_; lean_object* v_res_3328_; 
v_usedLetOnly_boxed_3325_ = lean_unbox(v_usedLetOnly_3315_);
v_skipConstInApp_boxed_3326_ = lean_unbox(v_skipConstInApp_3316_);
v_skipInstances_boxed_3327_ = lean_unbox(v_skipInstances_3317_);
v_res_3328_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3313_, v_post_3314_, v_usedLetOnly_boxed_3325_, v_skipConstInApp_boxed_3326_, v_skipInstances_boxed_3327_, v_e_3318_, v_a_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v_a_3319_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3329_, lean_object* v_post_3330_, lean_object* v_usedLetOnly_3331_, lean_object* v_skipConstInApp_3332_, lean_object* v_skipInstances_3333_, lean_object* v_fvars_3334_, lean_object* v_e_3335_, lean_object* v_a_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
uint8_t v_usedLetOnly_boxed_3342_; uint8_t v_skipConstInApp_boxed_3343_; uint8_t v_skipInstances_boxed_3344_; lean_object* v_res_3345_; 
v_usedLetOnly_boxed_3342_ = lean_unbox(v_usedLetOnly_3331_);
v_skipConstInApp_boxed_3343_ = lean_unbox(v_skipConstInApp_3332_);
v_skipInstances_boxed_3344_ = lean_unbox(v_skipInstances_3333_);
v_res_3345_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3329_, v_post_3330_, v_usedLetOnly_boxed_3342_, v_skipConstInApp_boxed_3343_, v_skipInstances_boxed_3344_, v_fvars_3334_, v_e_3335_, v_a_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v_a_3336_);
return v_res_3345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3346_, lean_object* v_post_3347_, lean_object* v_usedLetOnly_3348_, lean_object* v_skipConstInApp_3349_, lean_object* v_skipInstances_3350_, lean_object* v_fvars_3351_, lean_object* v_e_3352_, lean_object* v_a_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
uint8_t v_usedLetOnly_boxed_3359_; uint8_t v_skipConstInApp_boxed_3360_; uint8_t v_skipInstances_boxed_3361_; lean_object* v_res_3362_; 
v_usedLetOnly_boxed_3359_ = lean_unbox(v_usedLetOnly_3348_);
v_skipConstInApp_boxed_3360_ = lean_unbox(v_skipConstInApp_3349_);
v_skipInstances_boxed_3361_ = lean_unbox(v_skipInstances_3350_);
v_res_3362_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3346_, v_post_3347_, v_usedLetOnly_boxed_3359_, v_skipConstInApp_boxed_3360_, v_skipInstances_boxed_3361_, v_fvars_3351_, v_e_3352_, v_a_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec(v_a_3353_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3363_, lean_object* v_post_3364_, lean_object* v_usedLetOnly_3365_, lean_object* v_skipConstInApp_3366_, lean_object* v_skipInstances_3367_, lean_object* v_fvars_3368_, lean_object* v_e_3369_, lean_object* v_a_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
uint8_t v_usedLetOnly_boxed_3376_; uint8_t v_skipConstInApp_boxed_3377_; uint8_t v_skipInstances_boxed_3378_; lean_object* v_res_3379_; 
v_usedLetOnly_boxed_3376_ = lean_unbox(v_usedLetOnly_3365_);
v_skipConstInApp_boxed_3377_ = lean_unbox(v_skipConstInApp_3366_);
v_skipInstances_boxed_3378_ = lean_unbox(v_skipInstances_3367_);
v_res_3379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3363_, v_post_3364_, v_usedLetOnly_boxed_3376_, v_skipConstInApp_boxed_3377_, v_skipInstances_boxed_3378_, v_fvars_3368_, v_e_3369_, v_a_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v_a_3370_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3380_, lean_object* v___x_3381_, lean_object* v_pre_3382_, lean_object* v_post_3383_, lean_object* v_usedLetOnly_3384_, lean_object* v_skipConstInApp_3385_, lean_object* v_skipInstances_3386_, lean_object* v_a_3387_, lean_object* v_b_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v_usedLetOnly_boxed_3395_; uint8_t v_skipConstInApp_boxed_3396_; uint8_t v_skipInstances_boxed_3397_; lean_object* v_res_3398_; 
v_usedLetOnly_boxed_3395_ = lean_unbox(v_usedLetOnly_3384_);
v_skipConstInApp_boxed_3396_ = lean_unbox(v_skipConstInApp_3385_);
v_skipInstances_boxed_3397_ = lean_unbox(v_skipInstances_3386_);
v_res_3398_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3380_, v___x_3381_, v_pre_3382_, v_post_3383_, v_usedLetOnly_boxed_3395_, v_skipConstInApp_boxed_3396_, v_skipInstances_boxed_3397_, v_a_3387_, v_b_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___x_3381_);
lean_dec(v_upperBound_3380_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3399_, lean_object* v_pre_3400_, lean_object* v_post_3401_, lean_object* v_usedLetOnly_3402_, lean_object* v_skipConstInApp_3403_, lean_object* v_x_3404_, lean_object* v_x_3405_, lean_object* v_x_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
uint8_t v_skipInstances_boxed_3413_; uint8_t v_usedLetOnly_boxed_3414_; uint8_t v_skipConstInApp_boxed_3415_; lean_object* v_res_3416_; 
v_skipInstances_boxed_3413_ = lean_unbox(v_skipInstances_3399_);
v_usedLetOnly_boxed_3414_ = lean_unbox(v_usedLetOnly_3402_);
v_skipConstInApp_boxed_3415_ = lean_unbox(v_skipConstInApp_3403_);
v_res_3416_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3413_, v_pre_3400_, v_post_3401_, v_usedLetOnly_boxed_3414_, v_skipConstInApp_boxed_3415_, v_x_3404_, v_x_3405_, v_x_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
return v_res_3416_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3417_ = lean_box(0);
v___x_3418_ = lean_unsigned_to_nat(16u);
v___x_3419_ = lean_mk_array(v___x_3418_, v___x_3417_);
return v___x_3419_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3420_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0);
v___x_3421_ = lean_unsigned_to_nat(0u);
v___x_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3421_);
lean_ctor_set(v___x_3422_, 1, v___x_3420_);
return v___x_3422_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3423_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3424_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3424_, 0, lean_box(0));
lean_closure_set(v___x_3424_, 1, lean_box(0));
lean_closure_set(v___x_3424_, 2, v___x_3423_);
return v___x_3424_;
}
}
lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3425_, lean_object* v_pre_3426_, lean_object* v_post_3427_, uint8_t v_usedLetOnly_3428_, uint8_t v_skipConstInApp_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
uint8_t v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v_a_3438_; lean_object* v___x_3439_; 
v___x_3435_ = 0;
v___x_3436_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3437_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3436_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3426_, v_post_3427_, v_usedLetOnly_3428_, v_skipConstInApp_3429_, v___x_3435_, v_input_3425_, v_a_3438_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3449_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___x_3441_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3441_, 0, lean_box(0));
lean_closure_set(v___x_3441_, 1, lean_box(0));
lean_closure_set(v___x_3441_, 2, v_a_3438_);
v___x_3442_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3441_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; 
v_unused_3450_ = lean_ctor_get(v___x_3442_, 0);
lean_dec(v_unused_3450_);
v___x_3444_ = v___x_3442_;
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
else
{
lean_dec(v___x_3442_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3449_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___x_3447_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v_a_3440_);
v___x_3447_ = v___x_3444_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3440_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_dec(v_a_3438_);
return v___x_3439_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_3425_ = stack[0].m_obj;
lean_object* v_pre_3426_ = stack[1].m_obj;
lean_object* v_post_3427_ = stack[2].m_obj;
uint8_t v_usedLetOnly_3428_ = stack[3].m_num;
uint8_t v_skipConstInApp_3429_ = stack[4].m_num;
lean_object* v___y_3430_ = stack[5].m_obj;
lean_object* v___y_3431_ = stack[6].m_obj;
lean_object* v___y_3432_ = stack[7].m_obj;
lean_object* v___y_3433_ = stack[8].m_obj;
lean_object* v_res_3451_;
v_res_3451_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3425_, v_pre_3426_, v_post_3427_, v_usedLetOnly_3428_, v_skipConstInApp_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_);
stack->m_obj
 = v_res_3451_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3452_, lean_object* v_pre_3453_, lean_object* v_post_3454_, lean_object* v_usedLetOnly_3455_, lean_object* v_skipConstInApp_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
uint8_t v_usedLetOnly_boxed_3462_; uint8_t v_skipConstInApp_boxed_3463_; lean_object* v_res_3464_; 
v_usedLetOnly_boxed_3462_ = lean_unbox(v_usedLetOnly_3455_);
v_skipConstInApp_boxed_3463_ = lean_unbox(v_skipConstInApp_3456_);
v_res_3464_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3452_, v_pre_3453_, v_post_3454_, v_usedLetOnly_boxed_3462_, v_skipConstInApp_boxed_3463_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
return v_res_3464_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___f_3473_; lean_object* v___f_3474_; uint8_t v___x_3475_; lean_object* v___x_3476_; 
v___f_3473_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3474_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3475_ = 0;
v___x_3476_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3467_, v___f_3474_, v___f_3473_, v___x_3475_, v___x_3475_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
return v___x_3476_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3467_ = stack[0].m_obj;
lean_object* v_a_3468_ = stack[1].m_obj;
lean_object* v_a_3469_ = stack[2].m_obj;
lean_object* v_a_3470_ = stack[3].m_obj;
lean_object* v_a_3471_ = stack[4].m_obj;
lean_object* v_res_3477_;
v_res_3477_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
stack->m_obj
 = v_res_3477_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v_res_3484_; 
v_res_3484_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
lean_dec(v_a_3480_);
lean_dec_ref(v_a_3479_);
return v_res_3484_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_upperBound_3485_, lean_object* v___x_3486_, lean_object* v_pre_3487_, lean_object* v_post_3488_, uint8_t v_usedLetOnly_3489_, uint8_t v_skipConstInApp_3490_, uint8_t v_skipInstances_3491_, lean_object* v___x_3492_, lean_object* v_inst_3493_, lean_object* v_R_3494_, lean_object* v_a_3495_, lean_object* v_b_3496_, lean_object* v_c_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3485_, v___x_3486_, v_pre_3487_, v_post_3488_, v_usedLetOnly_3489_, v_skipConstInApp_3490_, v_skipInstances_3491_, v_a_3495_, v_b_3496_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
return v___x_3504_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_3485_ = stack[0].m_obj;
lean_object* v___x_3486_ = stack[1].m_obj;
lean_object* v_pre_3487_ = stack[2].m_obj;
lean_object* v_post_3488_ = stack[3].m_obj;
uint8_t v_usedLetOnly_3489_ = stack[4].m_num;
uint8_t v_skipConstInApp_3490_ = stack[5].m_num;
uint8_t v_skipInstances_3491_ = stack[6].m_num;
lean_object* v___x_3492_ = stack[7].m_obj;
lean_object* v_a_3495_ = stack[10].m_obj;
lean_object* v_b_3496_ = stack[11].m_obj;
lean_object* v___y_3498_ = stack[13].m_obj;
lean_object* v___y_3499_ = stack[14].m_obj;
lean_object* v___y_3500_ = stack[15].m_obj;
lean_object* v___y_3501_ = stack[16].m_obj;
lean_object* v___y_3502_ = stack[17].m_obj;
lean_object* v_res_3505_;
v_res_3505_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3485_, v___x_3486_, v_pre_3487_, v_post_3488_, v_usedLetOnly_3489_, v_skipConstInApp_3490_, v_skipInstances_3491_, v___x_3492_, lean_box(0), lean_box(0), v_a_3495_, v_b_3496_, lean_box(0), v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
stack->m_obj
 = v_res_3505_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_3506_ = _args[0];
lean_object* v___x_3507_ = _args[1];
lean_object* v_pre_3508_ = _args[2];
lean_object* v_post_3509_ = _args[3];
lean_object* v_usedLetOnly_3510_ = _args[4];
lean_object* v_skipConstInApp_3511_ = _args[5];
lean_object* v_skipInstances_3512_ = _args[6];
lean_object* v___x_3513_ = _args[7];
lean_object* v_inst_3514_ = _args[8];
lean_object* v_R_3515_ = _args[9];
lean_object* v_a_3516_ = _args[10];
lean_object* v_b_3517_ = _args[11];
lean_object* v_c_3518_ = _args[12];
lean_object* v___y_3519_ = _args[13];
lean_object* v___y_3520_ = _args[14];
lean_object* v___y_3521_ = _args[15];
lean_object* v___y_3522_ = _args[16];
lean_object* v___y_3523_ = _args[17];
lean_object* v___y_3524_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3525_; uint8_t v_skipConstInApp_boxed_3526_; uint8_t v_skipInstances_boxed_3527_; lean_object* v_res_3528_; 
v_usedLetOnly_boxed_3525_ = lean_unbox(v_usedLetOnly_3510_);
v_skipConstInApp_boxed_3526_ = lean_unbox(v_skipConstInApp_3511_);
v_skipInstances_boxed_3527_ = lean_unbox(v_skipInstances_3512_);
v_res_3528_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3506_, v___x_3507_, v_pre_3508_, v_post_3509_, v_usedLetOnly_boxed_3525_, v_skipConstInApp_boxed_3526_, v_skipInstances_boxed_3527_, v___x_3513_, v_inst_3514_, v_R_3515_, v_a_3516_, v_b_3517_, v_c_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___x_3513_);
lean_dec_ref(v___x_3507_);
lean_dec(v_upperBound_3506_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_00_u03b2_3529_, lean_object* v_m_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_3530_, v_a_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3533_, lean_object* v_m_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_00_u03b2_3533_, v_m_3534_, v_a_3535_);
lean_dec_ref(v_a_3535_);
lean_dec_ref(v_m_3534_);
return v_res_3536_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3537_, lean_object* v_name_3538_, uint8_t v_bi_3539_, lean_object* v_type_3540_, lean_object* v_k_3541_, uint8_t v_kind_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3538_, v_bi_3539_, v_type_3540_, v_k_3541_, v_kind_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
return v___x_3549_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3538_ = stack[1].m_obj;
uint8_t v_bi_3539_ = stack[2].m_num;
lean_object* v_type_3540_ = stack[3].m_obj;
lean_object* v_k_3541_ = stack[4].m_obj;
uint8_t v_kind_3542_ = stack[5].m_num;
lean_object* v___y_3543_ = stack[6].m_obj;
lean_object* v___y_3544_ = stack[7].m_obj;
lean_object* v___y_3545_ = stack[8].m_obj;
lean_object* v___y_3546_ = stack[9].m_obj;
lean_object* v___y_3547_ = stack[10].m_obj;
lean_object* v_res_3550_;
v_res_3550_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_box(0), v_name_3538_, v_bi_3539_, v_type_3540_, v_k_3541_, v_kind_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_);
stack->m_obj
 = v_res_3550_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3551_, lean_object* v_name_3552_, lean_object* v_bi_3553_, lean_object* v_type_3554_, lean_object* v_k_3555_, lean_object* v_kind_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
uint8_t v_bi_boxed_3563_; uint8_t v_kind_boxed_3564_; lean_object* v_res_3565_; 
v_bi_boxed_3563_ = lean_unbox(v_bi_3553_);
v_kind_boxed_3564_ = lean_unbox(v_kind_3556_);
v_res_3565_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3551_, v_name_3552_, v_bi_boxed_3563_, v_type_3554_, v_k_3555_, v_kind_boxed_3564_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
return v_res_3565_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3566_, lean_object* v_name_3567_, lean_object* v_type_3568_, lean_object* v_val_3569_, lean_object* v_k_3570_, uint8_t v_nondep_3571_, uint8_t v_kind_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3567_, v_type_3568_, v_val_3569_, v_k_3570_, v_nondep_3571_, v_kind_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
return v___x_3579_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_3567_ = stack[1].m_obj;
lean_object* v_type_3568_ = stack[2].m_obj;
lean_object* v_val_3569_ = stack[3].m_obj;
lean_object* v_k_3570_ = stack[4].m_obj;
uint8_t v_nondep_3571_ = stack[5].m_num;
uint8_t v_kind_3572_ = stack[6].m_num;
lean_object* v___y_3573_ = stack[7].m_obj;
lean_object* v___y_3574_ = stack[8].m_obj;
lean_object* v___y_3575_ = stack[9].m_obj;
lean_object* v___y_3576_ = stack[10].m_obj;
lean_object* v___y_3577_ = stack[11].m_obj;
lean_object* v_res_3580_;
v_res_3580_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_box(0), v_name_3567_, v_type_3568_, v_val_3569_, v_k_3570_, v_nondep_3571_, v_kind_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
stack->m_obj
 = v_res_3580_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3581_, lean_object* v_name_3582_, lean_object* v_type_3583_, lean_object* v_val_3584_, lean_object* v_k_3585_, lean_object* v_nondep_3586_, lean_object* v_kind_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
uint8_t v_nondep_boxed_3594_; uint8_t v_kind_boxed_3595_; lean_object* v_res_3596_; 
v_nondep_boxed_3594_ = lean_unbox(v_nondep_3586_);
v_kind_boxed_3595_ = lean_unbox(v_kind_3587_);
v_res_3596_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3581_, v_name_3582_, v_type_3583_, v_val_3584_, v_k_3585_, v_nondep_boxed_3594_, v_kind_boxed_3595_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
return v_res_3596_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3597_, lean_object* v_ref_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3598_);
return v___x_3604_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3598_ = stack[1].m_obj;
lean_object* v___y_3599_ = stack[2].m_obj;
lean_object* v___y_3600_ = stack[3].m_obj;
lean_object* v___y_3601_ = stack[4].m_obj;
lean_object* v___y_3602_ = stack[5].m_obj;
lean_object* v_res_3605_;
v_res_3605_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_box(0), v_ref_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
stack->m_obj
 = v_res_3605_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3606_, lean_object* v_ref_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_){
_start:
{
lean_object* v_res_3613_; 
v_res_3613_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3606_, v_ref_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_);
lean_dec(v___y_3611_);
lean_dec_ref(v___y_3610_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
return v_res_3613_;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3614_, lean_object* v_x_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT void l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3615_ = stack[1].m_obj;
lean_object* v___y_3616_ = stack[2].m_obj;
lean_object* v___y_3617_ = stack[3].m_obj;
lean_object* v___y_3618_ = stack[4].m_obj;
lean_object* v___y_3619_ = stack[5].m_obj;
lean_object* v___y_3620_ = stack[6].m_obj;
lean_object* v_res_3623_;
v_res_3623_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_box(0), v_x_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
stack->m_obj
 = v_res_3623_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3624_, lean_object* v_x_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3624_, v_x_3625_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3633_, lean_object* v_m_3634_, lean_object* v_a_3635_, lean_object* v_b_3636_){
_start:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3634_, v_a_3635_, v_b_3636_);
return v___x_3637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3638_, lean_object* v_a_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_3639_, v_x_3640_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b2_3642_, lean_object* v_a_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(v_00_u03b2_3642_, v_a_3643_, v_x_3644_);
lean_dec(v_x_3644_);
lean_dec_ref(v_a_3643_);
return v_res_3645_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3646_, lean_object* v_a_3647_, lean_object* v_x_3648_){
_start:
{
uint8_t v___x_3649_; 
v___x_3649_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3647_, v_x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3647_ = stack[1].m_obj;
lean_object* v_x_3648_ = stack[2].m_obj;
uint8_t v_res_3650_;
v_res_3650_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_box(0), v_a_3647_, v_x_3648_);
stack->m_num = v_res_3650_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3651_, lean_object* v_a_3652_, lean_object* v_x_3653_){
_start:
{
uint8_t v_res_3654_; lean_object* v_r_3655_; 
v_res_3654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3651_, v_a_3652_, v_x_3653_);
lean_dec(v_x_3653_);
lean_dec_ref(v_a_3652_);
v_r_3655_ = lean_box(v_res_3654_);
return v_r_3655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3656_, lean_object* v_data_3657_){
_start:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3657_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3659_, lean_object* v_a_3660_, lean_object* v_b_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3660_, v_b_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3664_, lean_object* v_i_3665_, lean_object* v_source_3666_, lean_object* v_target_3667_){
_start:
{
lean_object* v___x_3668_; 
v___x_3668_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3665_, v_source_3666_, v_target_3667_);
return v___x_3668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3669_, lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3670_, v_x_3671_);
return v___x_3672_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3673_, lean_object* v_opt_3674_){
_start:
{
lean_object* v_name_3675_; lean_object* v_defValue_3676_; lean_object* v_map_3677_; lean_object* v___x_3678_; 
v_name_3675_ = lean_ctor_get(v_opt_3674_, 0);
v_defValue_3676_ = lean_ctor_get(v_opt_3674_, 1);
v_map_3677_ = lean_ctor_get(v_opts_3673_, 0);
v___x_3678_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3677_, v_name_3675_);
if (lean_obj_tag(v___x_3678_) == 0)
{
uint8_t v___x_3679_; 
v___x_3679_ = lean_unbox(v_defValue_3676_);
return v___x_3679_;
}
else
{
lean_object* v_val_3680_; 
v_val_3680_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_val_3680_);
lean_dec_ref_known(v___x_3678_, 1);
if (lean_obj_tag(v_val_3680_) == 1)
{
uint8_t v_v_3681_; 
v_v_3681_ = lean_ctor_get_uint8(v_val_3680_, 0);
lean_dec_ref_known(v_val_3680_, 0);
return v_v_3681_;
}
else
{
uint8_t v___x_3682_; 
lean_dec(v_val_3680_);
v___x_3682_ = lean_unbox(v_defValue_3676_);
return v___x_3682_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_3673_ = stack[0].m_obj;
lean_object* v_opt_3674_ = stack[1].m_obj;
uint8_t v_res_3683_;
v_res_3683_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3673_, v_opt_3674_);
stack->m_num = v_res_3683_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3684_, lean_object* v_opt_3685_){
_start:
{
uint8_t v_res_3686_; lean_object* v_r_3687_; 
v_res_3686_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3684_, v_opt_3685_);
lean_dec_ref(v_opt_3685_);
lean_dec_ref(v_opts_3684_);
v_r_3687_ = lean_box(v_res_3686_);
return v_r_3687_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
return v___x_3689_;
}
}
lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg(){
_start:
{
lean_object* v___x_3691_; 
v___x_3691_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0);
return v___x_3691_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3692_;
v_res_3692_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
stack->m_obj
 = v_res_3692_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___boxed(lean_object* v___dummy_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
return v_res_3694_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3696_){
_start:
{
lean_object* v___x_3697_; 
v___x_3697_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
return v___x_3697_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(lean_object* v_e_3698_, lean_object* v_k_3699_, uint8_t v_cleanupAnnotations_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___f_3706_; uint8_t v___x_3707_; uint8_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___f_3706_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3706_, 0, v_k_3699_);
v___x_3707_ = 1;
v___x_3708_ = 0;
v___x_3709_ = lean_box(0);
v___x_3710_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3698_, v___x_3707_, v___x_3708_, v___x_3707_, v___x_3708_, v___x_3709_, v___f_3706_, v_cleanupAnnotations_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3710_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3710_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
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
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
v_a_3719_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___x_3710_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3710_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3724_; 
if (v_isShared_3722_ == 0)
{
v___x_3724_ = v___x_3721_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v_a_3719_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3698_ = stack[0].m_obj;
lean_object* v_k_3699_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_3700_ = stack[2].m_num;
lean_object* v___y_3701_ = stack[3].m_obj;
lean_object* v___y_3702_ = stack[4].m_obj;
lean_object* v___y_3703_ = stack[5].m_obj;
lean_object* v___y_3704_ = stack[6].m_obj;
lean_object* v_res_3727_;
v_res_3727_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3698_, v_k_3699_, v_cleanupAnnotations_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
stack->m_obj
 = v_res_3727_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg___boxed(lean_object* v_e_3728_, lean_object* v_k_3729_, lean_object* v_cleanupAnnotations_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3736_; lean_object* v_res_3737_; 
v_cleanupAnnotations_boxed_3736_ = lean_unbox(v_cleanupAnnotations_3730_);
v_res_3737_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3728_, v_k_3729_, v_cleanupAnnotations_boxed_3736_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
return v_res_3737_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_00_u03b1_3738_, lean_object* v_e_3739_, lean_object* v_k_3740_, uint8_t v_cleanupAnnotations_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3739_, v_k_3740_, v_cleanupAnnotations_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3739_ = stack[1].m_obj;
lean_object* v_k_3740_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_3741_ = stack[3].m_num;
lean_object* v___y_3742_ = stack[4].m_obj;
lean_object* v___y_3743_ = stack[5].m_obj;
lean_object* v___y_3744_ = stack[6].m_obj;
lean_object* v___y_3745_ = stack[7].m_obj;
lean_object* v_res_3748_;
v_res_3748_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_box(0), v_e_3739_, v_k_3740_, v_cleanupAnnotations_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
stack->m_obj
 = v_res_3748_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_00_u03b1_3749_, lean_object* v_e_3750_, lean_object* v_k_3751_, lean_object* v_cleanupAnnotations_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3758_; lean_object* v_res_3759_; 
v_cleanupAnnotations_boxed_3758_ = lean_unbox(v_cleanupAnnotations_3752_);
v_res_3759_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(v_00_u03b1_3749_, v_e_3750_, v_k_3751_, v_cleanupAnnotations_boxed_3758_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
return v_res_3759_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3760_, lean_object* v_x_3761_, lean_object* v_x_3762_){
_start:
{
if (lean_obj_tag(v_x_3760_) == 5)
{
lean_object* v_fn_3767_; lean_object* v_arg_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v_fn_3767_ = lean_ctor_get(v_x_3760_, 0);
lean_inc_ref(v_fn_3767_);
v_arg_3768_ = lean_ctor_get(v_x_3760_, 1);
lean_inc_ref(v_arg_3768_);
lean_dec_ref_known(v_x_3760_, 2);
v___x_3769_ = lean_array_set(v_x_3761_, v_x_3762_, v_arg_3768_);
v___x_3770_ = lean_unsigned_to_nat(1u);
v___x_3771_ = lean_nat_sub(v_x_3762_, v___x_3770_);
lean_dec(v_x_3762_);
v_x_3760_ = v_fn_3767_;
v_x_3761_ = v___x_3769_;
v_x_3762_ = v___x_3771_;
goto _start;
}
else
{
lean_object* v___x_3773_; uint8_t v___x_3774_; 
lean_dec(v_x_3762_);
v___x_3773_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3774_ = l_Lean_Expr_isConstOf(v_x_3760_, v___x_3773_);
lean_dec_ref(v_x_3760_);
if (v___x_3774_ == 0)
{
lean_dec_ref(v_x_3761_);
goto v___jp_3764_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = lean_unsigned_to_nat(2u);
v___x_3776_ = lean_array_get_size(v_x_3761_);
v___x_3777_ = lean_nat_dec_le(v___x_3775_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_dec_ref(v_x_3761_);
goto v___jp_3764_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3778_ = lean_unsigned_to_nat(1u);
v___x_3779_ = lean_array_fget(v_x_3761_, v___x_3778_);
v___x_3780_ = l_Array_toSubarray___redArg(v_x_3761_, v___x_3775_, v___x_3776_);
v___x_3781_ = l_Subarray_copy___redArg(v___x_3780_);
v___x_3782_ = l_Lean_mkAppN(v___x_3779_, v___x_3781_);
lean_dec_ref(v___x_3781_);
v___x_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
v___x_3784_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
return v___x_3785_;
}
}
}
v___jp_3764_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3765_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
return v___x_3766_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3760_ = stack[0].m_obj;
lean_object* v_x_3761_ = stack[1].m_obj;
lean_object* v_x_3762_ = stack[2].m_obj;
lean_object* v_res_3786_;
v_res_3786_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3760_, v_x_3761_, v_x_3762_);
stack->m_obj
 = v_res_3786_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3787_, lean_object* v_x_3788_, lean_object* v_x_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3787_, v_x_3788_, v_x_3789_);
return v_res_3791_;
}
}
lean_object* l_Lean_Elab_WF_preprocess___lam__0(lean_object* v_e_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
lean_object* v_dummy_3798_; lean_object* v_nargs_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_dummy_3798_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3799_ = l_Lean_Expr_getAppNumArgs(v_e_3792_);
lean_inc(v_nargs_3799_);
v___x_3800_ = lean_mk_array(v_nargs_3799_, v_dummy_3798_);
v___x_3801_ = lean_unsigned_to_nat(1u);
v___x_3802_ = lean_nat_sub(v_nargs_3799_, v___x_3801_);
lean_dec(v_nargs_3799_);
v___x_3803_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3792_, v___x_3800_, v___x_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT void l_Lean_Elab_WF_preprocess___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3792_ = stack[0].m_obj;
lean_object* v___y_3793_ = stack[1].m_obj;
lean_object* v___y_3794_ = stack[2].m_obj;
lean_object* v___y_3795_ = stack[3].m_obj;
lean_object* v___y_3796_ = stack[4].m_obj;
lean_object* v_res_3804_;
v_res_3804_ = l_Lean_Elab_WF_preprocess___lam__0(v_e_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
stack->m_obj
 = v_res_3804_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v_e_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Elab_WF_preprocess___lam__0(v_e_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
return v_res_3811_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(lean_object* v_ref_3812_){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3814_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_ref_3812_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_3812_ = stack[0].m_obj;
lean_object* v_res_3817_;
v_res_3817_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3812_);
stack->m_obj
 = v_res_3817_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_ref_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3818_);
return v_res_3820_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3821_ = lean_box(0);
v___x_3822_ = l_Lean_interruptExceptionId;
v___x_3823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
lean_ctor_set(v___x_3823_, 1, v___x_3821_);
return v___x_3823_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg(){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3825_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3825_);
return v___x_3826_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3827_;
v_res_3827_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
stack->m_obj
 = v_res_3827_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v___y_3828_){
_start:
{
lean_object* v_res_3829_; 
v_res_3829_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v_res_3829_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(lean_object* v_x_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v___y_3838_; lean_object* v___y_3848_; uint8_t v___y_3849_; uint16_t v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; uint8_t v___y_3853_; lean_object* v_toCold_3858_; lean_object* v_currRecDepth_3859_; lean_object* v_ref_3860_; uint16_t v_optionFlags_3861_; uint8_t v_suppressElabErrors_3862_; uint8_t v_isRecordingDeps_3863_; lean_object* v_maxRecDepth_3864_; lean_object* v_cancelTk_x3f_3865_; 
v_toCold_3858_ = lean_ctor_get(v___y_3834_, 0);
v_currRecDepth_3859_ = lean_ctor_get(v___y_3834_, 1);
v_ref_3860_ = lean_ctor_get(v___y_3834_, 2);
v_optionFlags_3861_ = lean_ctor_get_uint16(v___y_3834_, sizeof(void*)*3);
v_suppressElabErrors_3862_ = lean_ctor_get_uint8(v___y_3834_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3863_ = lean_ctor_get_uint8(v___y_3834_, sizeof(void*)*3 + 3);
v_maxRecDepth_3864_ = lean_ctor_get(v_toCold_3858_, 3);
v_cancelTk_x3f_3865_ = lean_ctor_get(v_toCold_3858_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3865_) == 1)
{
lean_object* v_val_3871_; uint8_t v___x_3872_; 
v_val_3871_ = lean_ctor_get(v_cancelTk_x3f_3865_, 0);
v___x_3872_ = l_IO_CancelToken_isSet(v_val_3871_);
if (v___x_3872_ == 0)
{
goto v___jp_3866_;
}
else
{
lean_object* v___x_3873_; lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3881_; 
lean_dec_ref(v_x_3830_);
v___x_3873_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3881_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3881_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3881_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___x_3879_; 
if (v_isShared_3877_ == 0)
{
v___x_3879_ = v___x_3876_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3880_; 
v_reuseFailAlloc_3880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3880_, 0, v_a_3874_);
v___x_3879_ = v_reuseFailAlloc_3880_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
return v___x_3879_;
}
}
}
}
else
{
goto v___jp_3866_;
}
v___jp_3837_:
{
if (lean_obj_tag(v___y_3838_) == 0)
{
return v___y_3838_;
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
v_a_3839_ = lean_ctor_get(v___y_3838_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___y_3838_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___y_3838_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___y_3838_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
v___jp_3847_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3854_ = lean_unsigned_to_nat(1u);
v___x_3855_ = lean_nat_add(v___y_3848_, v___x_3854_);
lean_inc_ref(v___y_3851_);
v___x_3856_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3856_, 0, v___y_3851_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
lean_ctor_set(v___x_3856_, 2, v___y_3852_);
lean_ctor_set_uint16(v___x_3856_, sizeof(void*)*3, v___y_3850_);
lean_ctor_set_uint8(v___x_3856_, sizeof(void*)*3 + 2, v___y_3849_);
lean_ctor_set_uint8(v___x_3856_, sizeof(void*)*3 + 3, v___y_3853_);
lean_inc(v___y_3835_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc(v___y_3831_);
v___x_3857_ = lean_apply_6(v_x_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___x_3856_, v___y_3835_, lean_box(0));
v___y_3838_ = v___x_3857_;
goto v___jp_3837_;
}
v___jp_3866_:
{
lean_object* v___x_3867_; uint8_t v___x_3868_; 
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = lean_nat_dec_eq(v_maxRecDepth_3864_, v___x_3867_);
if (v___x_3868_ == 0)
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_nat_dec_eq(v_currRecDepth_3859_, v_maxRecDepth_3864_);
if (v___x_3869_ == 0)
{
lean_inc(v_ref_3860_);
v___y_3848_ = v_currRecDepth_3859_;
v___y_3849_ = v_suppressElabErrors_3862_;
v___y_3850_ = v_optionFlags_3861_;
v___y_3851_ = v_toCold_3858_;
v___y_3852_ = v_ref_3860_;
v___y_3853_ = v_isRecordingDeps_3863_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3870_; 
lean_dec_ref(v_x_3830_);
lean_inc(v_ref_3860_);
v___x_3870_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3860_);
v___y_3838_ = v___x_3870_;
goto v___jp_3837_;
}
}
else
{
lean_inc(v_ref_3860_);
v___y_3848_ = v_currRecDepth_3859_;
v___y_3849_ = v_suppressElabErrors_3862_;
v___y_3850_ = v_optionFlags_3861_;
v___y_3851_ = v_toCold_3858_;
v___y_3852_ = v_ref_3860_;
v___y_3853_ = v_isRecordingDeps_3863_;
goto v___jp_3847_;
}
}
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3830_ = stack[0].m_obj;
lean_object* v___y_3831_ = stack[1].m_obj;
lean_object* v___y_3832_ = stack[2].m_obj;
lean_object* v___y_3833_ = stack[3].m_obj;
lean_object* v___y_3834_ = stack[4].m_obj;
lean_object* v___y_3835_ = stack[5].m_obj;
lean_object* v_res_3882_;
v_res_3882_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
stack->m_obj
 = v_res_3882_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg___boxed(lean_object* v_x_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
return v_res_3890_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(lean_object* v_pre_3891_, lean_object* v_post_3892_, size_t v_sz_3893_, size_t v_i_3894_, lean_object* v_bs_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
uint8_t v___x_3902_; 
v___x_3902_ = lean_usize_dec_lt(v_i_3894_, v_sz_3893_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; 
lean_dec_ref(v_post_3892_);
lean_dec_ref(v_pre_3891_);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_bs_3895_);
return v___x_3903_;
}
else
{
lean_object* v_v_3904_; lean_object* v___x_3905_; lean_object* v_bs_x27_3906_; lean_object* v___x_3907_; 
v_v_3904_ = lean_array_uget(v_bs_3895_, v_i_3894_);
v___x_3905_ = lean_unsigned_to_nat(0u);
v_bs_x27_3906_ = lean_array_uset(v_bs_3895_, v_i_3894_, v___x_3905_);
lean_inc_ref(v_post_3892_);
lean_inc_ref(v_pre_3891_);
v___x_3907_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3891_, v_post_3892_, v_v_3904_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; size_t v___x_3909_; size_t v___x_3910_; lean_object* v___x_3911_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = ((size_t)1ULL);
v___x_3910_ = lean_usize_add(v_i_3894_, v___x_3909_);
v___x_3911_ = lean_array_uset(v_bs_x27_3906_, v_i_3894_, v_a_3908_);
v_i_3894_ = v___x_3910_;
v_bs_3895_ = v___x_3911_;
goto _start;
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec_ref(v_bs_x27_3906_);
lean_dec_ref(v_post_3892_);
lean_dec_ref(v_pre_3891_);
v_a_3913_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3907_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3907_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3891_ = stack[0].m_obj;
lean_object* v_post_3892_ = stack[1].m_obj;
size_t v_sz_3893_ = stack[2].m_num;
size_t v_i_3894_ = stack[3].m_num;
lean_object* v_bs_3895_ = stack[4].m_obj;
lean_object* v___y_3896_ = stack[5].m_obj;
lean_object* v___y_3897_ = stack[6].m_obj;
lean_object* v___y_3898_ = stack[7].m_obj;
lean_object* v___y_3899_ = stack[8].m_obj;
lean_object* v___y_3900_ = stack[9].m_obj;
lean_object* v_res_3921_;
v_res_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_3891_, v_post_3892_, v_sz_3893_, v_i_3894_, v_bs_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
stack->m_obj
 = v_res_3921_;
}
lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_3922_, lean_object* v_post_3923_, lean_object* v_x_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
if (lean_obj_tag(v_x_3924_) == 5)
{
lean_object* v_fn_3933_; lean_object* v_arg_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
v_fn_3933_ = lean_ctor_get(v_x_3924_, 0);
lean_inc_ref(v_fn_3933_);
v_arg_3934_ = lean_ctor_get(v_x_3924_, 1);
lean_inc_ref(v_arg_3934_);
lean_dec_ref_known(v_x_3924_, 2);
v___x_3935_ = lean_array_set(v_x_3925_, v_x_3926_, v_arg_3934_);
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_3937_ = lean_nat_sub(v_x_3926_, v___x_3936_);
lean_dec(v_x_3926_);
v_x_3924_ = v_fn_3933_;
v_x_3925_ = v___x_3935_;
v_x_3926_ = v___x_3937_;
goto _start;
}
else
{
lean_object* v___x_3939_; 
lean_dec(v_x_3926_);
lean_inc_ref(v_post_3923_);
lean_inc_ref(v_pre_3922_);
v___x_3939_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3922_, v_post_3923_, v_x_3924_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; size_t v_sz_3941_; size_t v___x_3942_; lean_object* v___x_3943_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v_sz_3941_ = lean_array_size(v_x_3925_);
v___x_3942_ = ((size_t)0ULL);
lean_inc_ref(v_post_3923_);
lean_inc_ref(v_pre_3922_);
v___x_3943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_3922_, v_post_3923_, v_sz_3941_, v___x_3942_, v_x_3925_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_a_3944_);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = l_Lean_mkAppN(v_a_3940_, v_a_3944_);
lean_dec(v_a_3944_);
v___x_3946_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3922_, v_post_3923_, v___x_3945_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
return v___x_3946_;
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec(v_a_3940_);
lean_dec_ref(v_post_3923_);
lean_dec_ref(v_pre_3922_);
v_a_3947_ = lean_ctor_get(v___x_3943_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3943_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3943_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_dec_ref(v_x_3925_);
lean_dec_ref(v_post_3923_);
lean_dec_ref(v_pre_3922_);
return v___x_3939_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_3922_ = stack[0].m_obj;
lean_object* v_post_3923_ = stack[1].m_obj;
lean_object* v_x_3924_ = stack[2].m_obj;
lean_object* v_x_3925_ = stack[3].m_obj;
lean_object* v_x_3926_ = stack[4].m_obj;
lean_object* v___y_3927_ = stack[5].m_obj;
lean_object* v___y_3928_ = stack[6].m_obj;
lean_object* v___y_3929_ = stack[7].m_obj;
lean_object* v___y_3930_ = stack[8].m_obj;
lean_object* v___y_3931_ = stack[9].m_obj;
lean_object* v_res_3955_;
v_res_3955_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3922_, v_post_3923_, v_x_3924_, v_x_3925_, v_x_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
stack->m_obj
 = v_res_3955_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v___x_3956_, lean_object* v_pre_3957_, lean_object* v_e_3958_, lean_object* v_post_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Core_checkSystem(v___x_3956_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v___x_3967_; 
lean_dec_ref_known(v___x_3966_, 1);
lean_inc_ref(v_pre_3957_);
lean_inc(v___y_3964_);
lean_inc_ref(v___y_3963_);
lean_inc(v___y_3962_);
lean_inc_ref(v___y_3961_);
lean_inc_ref(v_e_3958_);
v___x_3967_ = lean_apply_6(v_pre_3957_, v_e_3958_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_, lean_box(0));
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4083_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_3970_ = v___x_3967_;
v_isShared_3971_ = v_isSharedCheck_4083_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4083_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___y_3973_; 
switch(lean_obj_tag(v_a_3968_))
{
case 0:
{
lean_object* v_e_4073_; lean_object* v___x_4075_; 
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_e_3958_);
lean_dec_ref(v_pre_3957_);
v_e_4073_ = lean_ctor_get(v_a_3968_, 0);
lean_inc_ref(v_e_4073_);
lean_dec_ref_known(v_a_3968_, 1);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v_e_4073_);
v___x_4075_ = v___x_3970_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_e_4073_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
case 1:
{
lean_object* v_e_4077_; lean_object* v___x_4078_; 
lean_del_object(v___x_3970_);
lean_dec_ref(v_e_3958_);
v_e_4077_ = lean_ctor_get(v_a_3968_, 0);
lean_inc_ref(v_e_4077_);
lean_dec_ref_known(v_a_3968_, 1);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4078_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_e_4077_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v_a_4079_; lean_object* v___x_4080_; 
v_a_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc(v_a_4079_);
lean_dec_ref_known(v___x_4078_, 1);
v___x_4080_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v_a_4079_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4080_;
}
else
{
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4078_;
}
}
default: 
{
lean_object* v_e_x3f_4081_; 
lean_del_object(v___x_3970_);
v_e_x3f_4081_ = lean_ctor_get(v_a_3968_, 0);
lean_inc(v_e_x3f_4081_);
lean_dec_ref_known(v_a_3968_, 1);
if (lean_obj_tag(v_e_x3f_4081_) == 0)
{
v___y_3973_ = v_e_3958_;
goto v___jp_3972_;
}
else
{
lean_object* v_val_4082_; 
lean_dec_ref(v_e_3958_);
v_val_4082_ = lean_ctor_get(v_e_x3f_4081_, 0);
lean_inc(v_val_4082_);
lean_dec_ref_known(v_e_x3f_4081_, 1);
v___y_3973_ = v_val_4082_;
goto v___jp_3972_;
}
}
}
v___jp_3972_:
{
switch(lean_obj_tag(v___y_3973_))
{
case 7:
{
lean_object* v_binderName_3974_; lean_object* v_binderType_3975_; lean_object* v_body_3976_; uint8_t v_binderInfo_3977_; lean_object* v___x_3978_; 
v_binderName_3974_ = lean_ctor_get(v___y_3973_, 0);
v_binderType_3975_ = lean_ctor_get(v___y_3973_, 1);
v_body_3976_ = lean_ctor_get(v___y_3973_, 2);
v_binderInfo_3977_ = lean_ctor_get_uint8(v___y_3973_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3975_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_3978_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_binderType_3975_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v_a_3979_; lean_object* v___x_3980_; 
v_a_3979_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_a_3979_);
lean_dec_ref_known(v___x_3978_, 1);
lean_inc_ref(v_body_3976_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_3980_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_body_3976_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; size_t v___x_3982_; size_t v___x_3983_; uint8_t v___x_3984_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
lean_inc(v_a_3981_);
lean_dec_ref_known(v___x_3980_, 1);
v___x_3982_ = lean_ptr_addr(v_binderType_3975_);
v___x_3983_ = lean_ptr_addr(v_a_3979_);
v___x_3984_ = lean_usize_dec_eq(v___x_3982_, v___x_3983_);
if (v___x_3984_ == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3986_; 
lean_inc(v_binderName_3974_);
lean_dec_ref_known(v___y_3973_, 3);
v___x_3985_ = l_Lean_Expr_forallE___override(v_binderName_3974_, v_a_3979_, v_a_3981_, v_binderInfo_3977_);
v___x_3986_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_3985_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3986_;
}
else
{
size_t v___x_3987_; size_t v___x_3988_; uint8_t v___x_3989_; 
v___x_3987_ = lean_ptr_addr(v_body_3976_);
v___x_3988_ = lean_ptr_addr(v_a_3981_);
v___x_3989_ = lean_usize_dec_eq(v___x_3987_, v___x_3988_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_inc(v_binderName_3974_);
lean_dec_ref_known(v___y_3973_, 3);
v___x_3990_ = l_Lean_Expr_forallE___override(v_binderName_3974_, v_a_3979_, v_a_3981_, v_binderInfo_3977_);
v___x_3991_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_3990_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3991_;
}
else
{
uint8_t v___x_3992_; 
v___x_3992_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3977_, v_binderInfo_3977_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
lean_inc(v_binderName_3974_);
lean_dec_ref_known(v___y_3973_, 3);
v___x_3993_ = l_Lean_Expr_forallE___override(v_binderName_3974_, v_a_3979_, v_a_3981_, v_binderInfo_3977_);
v___x_3994_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_3993_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3994_;
}
else
{
lean_object* v___x_3995_; 
lean_dec(v_a_3981_);
lean_dec(v_a_3979_);
v___x_3995_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___y_3973_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_3995_;
}
}
}
}
else
{
lean_dec(v_a_3979_);
lean_dec_ref_known(v___y_3973_, 3);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_3980_;
}
}
else
{
lean_dec_ref_known(v___y_3973_, 3);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_3978_;
}
}
case 6:
{
lean_object* v_binderName_3996_; lean_object* v_binderType_3997_; lean_object* v_body_3998_; uint8_t v_binderInfo_3999_; lean_object* v___x_4000_; 
v_binderName_3996_ = lean_ctor_get(v___y_3973_, 0);
v_binderType_3997_ = lean_ctor_get(v___y_3973_, 1);
v_body_3998_ = lean_ctor_get(v___y_3973_, 2);
v_binderInfo_3999_ = lean_ctor_get_uint8(v___y_3973_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3997_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4000_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_binderType_3997_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4002_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_a_4001_);
lean_dec_ref_known(v___x_4000_, 1);
lean_inc_ref(v_body_3998_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4002_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_body_3998_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; size_t v___x_4004_; size_t v___x_4005_; uint8_t v___x_4006_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v___x_4002_, 1);
v___x_4004_ = lean_ptr_addr(v_binderType_3997_);
v___x_4005_ = lean_ptr_addr(v_a_4001_);
v___x_4006_ = lean_usize_dec_eq(v___x_4004_, v___x_4005_);
if (v___x_4006_ == 0)
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
lean_inc(v_binderName_3996_);
lean_dec_ref_known(v___y_3973_, 3);
v___x_4007_ = l_Lean_Expr_lam___override(v_binderName_3996_, v_a_4001_, v_a_4003_, v_binderInfo_3999_);
v___x_4008_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4007_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4008_;
}
else
{
size_t v___x_4009_; size_t v___x_4010_; uint8_t v___x_4011_; 
v___x_4009_ = lean_ptr_addr(v_body_3998_);
v___x_4010_ = lean_ptr_addr(v_a_4003_);
v___x_4011_ = lean_usize_dec_eq(v___x_4009_, v___x_4010_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4013_; 
lean_inc(v_binderName_3996_);
lean_dec_ref_known(v___y_3973_, 3);
v___x_4012_ = l_Lean_Expr_lam___override(v_binderName_3996_, v_a_4001_, v_a_4003_, v_binderInfo_3999_);
v___x_4013_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4012_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4013_;
}
else
{
uint8_t v___x_4014_; 
v___x_4014_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3999_, v_binderInfo_3999_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_inc(v_binderName_3996_);
lean_dec_ref_known(v___y_3973_, 3);
v___x_4015_ = l_Lean_Expr_lam___override(v_binderName_3996_, v_a_4001_, v_a_4003_, v_binderInfo_3999_);
v___x_4016_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4015_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4016_;
}
else
{
lean_object* v___x_4017_; 
lean_dec(v_a_4003_);
lean_dec(v_a_4001_);
v___x_4017_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___y_3973_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4017_;
}
}
}
}
else
{
lean_dec(v_a_4001_);
lean_dec_ref_known(v___y_3973_, 3);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4002_;
}
}
else
{
lean_dec_ref_known(v___y_3973_, 3);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4000_;
}
}
case 8:
{
lean_object* v_declName_4018_; lean_object* v_type_4019_; lean_object* v_value_4020_; lean_object* v_body_4021_; uint8_t v_nondep_4022_; lean_object* v___x_4023_; 
v_declName_4018_ = lean_ctor_get(v___y_3973_, 0);
v_type_4019_ = lean_ctor_get(v___y_3973_, 1);
v_value_4020_ = lean_ctor_get(v___y_3973_, 2);
v_body_4021_ = lean_ctor_get(v___y_3973_, 3);
v_nondep_4022_ = lean_ctor_get_uint8(v___y_3973_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_4019_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4023_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_type_4019_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
lean_inc_ref(v_value_4020_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4025_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_value_4020_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4027_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref_known(v___x_4025_, 1);
lean_inc_ref(v_body_4021_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4027_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_body_4021_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; size_t v___x_4029_; size_t v___x_4030_; uint8_t v___x_4031_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = lean_ptr_addr(v_type_4019_);
v___x_4030_ = lean_ptr_addr(v_a_4024_);
v___x_4031_ = lean_usize_dec_eq(v___x_4029_, v___x_4030_);
if (v___x_4031_ == 0)
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
lean_inc(v_declName_4018_);
lean_dec_ref_known(v___y_3973_, 4);
v___x_4032_ = l_Lean_Expr_letE___override(v_declName_4018_, v_a_4024_, v_a_4026_, v_a_4028_, v_nondep_4022_);
v___x_4033_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4032_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4033_;
}
else
{
size_t v___x_4034_; size_t v___x_4035_; uint8_t v___x_4036_; 
v___x_4034_ = lean_ptr_addr(v_value_4020_);
v___x_4035_ = lean_ptr_addr(v_a_4026_);
v___x_4036_ = lean_usize_dec_eq(v___x_4034_, v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
lean_inc(v_declName_4018_);
lean_dec_ref_known(v___y_3973_, 4);
v___x_4037_ = l_Lean_Expr_letE___override(v_declName_4018_, v_a_4024_, v_a_4026_, v_a_4028_, v_nondep_4022_);
v___x_4038_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4037_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4038_;
}
else
{
size_t v___x_4039_; size_t v___x_4040_; uint8_t v___x_4041_; 
v___x_4039_ = lean_ptr_addr(v_body_4021_);
v___x_4040_ = lean_ptr_addr(v_a_4028_);
v___x_4041_ = lean_usize_dec_eq(v___x_4039_, v___x_4040_);
if (v___x_4041_ == 0)
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
lean_inc(v_declName_4018_);
lean_dec_ref_known(v___y_3973_, 4);
v___x_4042_ = l_Lean_Expr_letE___override(v_declName_4018_, v_a_4024_, v_a_4026_, v_a_4028_, v_nondep_4022_);
v___x_4043_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4042_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4043_;
}
else
{
lean_object* v___x_4044_; 
lean_dec(v_a_4028_);
lean_dec(v_a_4026_);
lean_dec(v_a_4024_);
v___x_4044_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___y_3973_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4044_;
}
}
}
}
else
{
lean_dec(v_a_4026_);
lean_dec(v_a_4024_);
lean_dec_ref_known(v___y_3973_, 4);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4027_;
}
}
else
{
lean_dec(v_a_4024_);
lean_dec_ref_known(v___y_3973_, 4);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4025_;
}
}
else
{
lean_dec_ref_known(v___y_3973_, 4);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4023_;
}
}
case 5:
{
lean_object* v_dummy_4045_; lean_object* v_nargs_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_dummy_4045_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_4046_ = l_Lean_Expr_getAppNumArgs(v___y_3973_);
lean_inc(v_nargs_4046_);
v___x_4047_ = lean_mk_array(v_nargs_4046_, v_dummy_4045_);
v___x_4048_ = lean_unsigned_to_nat(1u);
v___x_4049_ = lean_nat_sub(v_nargs_4046_, v___x_4048_);
lean_dec(v_nargs_4046_);
v___x_4050_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3957_, v_post_3959_, v___y_3973_, v___x_4047_, v___x_4049_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4050_;
}
case 10:
{
lean_object* v_data_4051_; lean_object* v_expr_4052_; lean_object* v___x_4053_; 
v_data_4051_ = lean_ctor_get(v___y_3973_, 0);
v_expr_4052_ = lean_ctor_get(v___y_3973_, 1);
lean_inc_ref(v_expr_4052_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4053_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_expr_4052_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; size_t v___x_4055_; size_t v___x_4056_; uint8_t v___x_4057_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref_known(v___x_4053_, 1);
v___x_4055_ = lean_ptr_addr(v_expr_4052_);
v___x_4056_ = lean_ptr_addr(v_a_4054_);
v___x_4057_ = lean_usize_dec_eq(v___x_4055_, v___x_4056_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_inc(v_data_4051_);
lean_dec_ref_known(v___y_3973_, 2);
v___x_4058_ = l_Lean_Expr_mdata___override(v_data_4051_, v_a_4054_);
v___x_4059_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4058_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4059_;
}
else
{
lean_object* v___x_4060_; 
lean_dec(v_a_4054_);
v___x_4060_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___y_3973_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4060_;
}
}
else
{
lean_dec_ref_known(v___y_3973_, 2);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4053_;
}
}
case 11:
{
lean_object* v_typeName_4061_; lean_object* v_idx_4062_; lean_object* v_struct_4063_; lean_object* v___x_4064_; 
v_typeName_4061_ = lean_ctor_get(v___y_3973_, 0);
v_idx_4062_ = lean_ctor_get(v___y_3973_, 1);
v_struct_4063_ = lean_ctor_get(v___y_3973_, 2);
lean_inc_ref(v_struct_4063_);
lean_inc_ref(v_post_3959_);
lean_inc_ref(v_pre_3957_);
v___x_4064_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3957_, v_post_3959_, v_struct_4063_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; size_t v___x_4066_; size_t v___x_4067_; uint8_t v___x_4068_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v___x_4064_, 1);
v___x_4066_ = lean_ptr_addr(v_struct_4063_);
v___x_4067_ = lean_ptr_addr(v_a_4065_);
v___x_4068_ = lean_usize_dec_eq(v___x_4066_, v___x_4067_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
lean_inc(v_idx_4062_);
lean_inc(v_typeName_4061_);
lean_dec_ref_known(v___y_3973_, 3);
v___x_4069_ = l_Lean_Expr_proj___override(v_typeName_4061_, v_idx_4062_, v_a_4065_);
v___x_4070_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___x_4069_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4070_;
}
else
{
lean_object* v___x_4071_; 
lean_dec(v_a_4065_);
v___x_4071_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___y_3973_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4071_;
}
}
else
{
lean_dec_ref_known(v___y_3973_, 3);
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_pre_3957_);
return v___x_4064_;
}
}
default: 
{
lean_object* v___x_4072_; 
v___x_4072_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3957_, v_post_3959_, v___y_3973_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
return v___x_4072_;
}
}
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_e_3958_);
lean_dec_ref(v_pre_3957_);
v_a_4084_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_3967_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_3967_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v_post_3959_);
lean_dec_ref(v_e_3958_);
lean_dec_ref(v_pre_3957_);
v_a_4092_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_3966_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_3966_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3956_ = stack[0].m_obj;
lean_object* v_pre_3957_ = stack[1].m_obj;
lean_object* v_e_3958_ = stack[2].m_obj;
lean_object* v_post_3959_ = stack[3].m_obj;
lean_object* v___y_3960_ = stack[4].m_obj;
lean_object* v___y_3961_ = stack[5].m_obj;
lean_object* v___y_3962_ = stack[6].m_obj;
lean_object* v___y_3963_ = stack[7].m_obj;
lean_object* v___y_3964_ = stack[8].m_obj;
lean_object* v_res_4100_;
v_res_4100_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v___x_3956_, v_pre_3957_, v_e_3958_, v_post_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
stack->m_obj
 = v_res_4100_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v___x_4101_, lean_object* v_pre_4102_, lean_object* v_e_4103_, lean_object* v_post_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v___x_4101_, v_pre_4102_, v_e_4103_, v_post_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
return v_res_4111_;
}
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_4112_, lean_object* v_post_4113_, lean_object* v_e_4114_, lean_object* v_a_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
lean_inc(v_a_4115_);
v___x_4121_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4121_, 0, lean_box(0));
lean_closure_set(v___x_4121_, 1, lean_box(0));
lean_closure_set(v___x_4121_, 2, v_a_4115_);
v___x_4122_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_4121_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4154_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4154_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4154_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_4123_, v_e_4114_);
lean_dec(v_a_4123_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v___x_4128_; lean_object* v___f_4129_; lean_object* v___x_4130_; 
lean_del_object(v___x_4125_);
v___x_4128_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
lean_inc_ref(v_e_4114_);
v___f_4129_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4129_, 0, v___x_4128_);
lean_closure_set(v___f_4129_, 1, v_pre_4112_);
lean_closure_set(v___f_4129_, 2, v_e_4114_);
lean_closure_set(v___f_4129_, 3, v_post_4113_);
v___x_4130_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v___f_4129_, v_a_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___f_4132_; lean_object* v___x_4133_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc_n(v_a_4131_, 2);
lean_dec_ref_known(v___x_4130_, 1);
lean_inc(v_a_4115_);
v___f_4132_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4132_, 0, v_a_4115_);
lean_closure_set(v___f_4132_, 1, v_e_4114_);
lean_closure_set(v___f_4132_, 2, v_a_4131_);
v___x_4133_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_4132_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v___x_4135_; uint8_t v_isShared_4136_; uint8_t v_isSharedCheck_4140_; 
v_isSharedCheck_4140_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; 
v_unused_4141_ = lean_ctor_get(v___x_4133_, 0);
lean_dec(v_unused_4141_);
v___x_4135_ = v___x_4133_;
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
else
{
lean_dec(v___x_4133_);
v___x_4135_ = lean_box(0);
v_isShared_4136_ = v_isSharedCheck_4140_;
goto v_resetjp_4134_;
}
v_resetjp_4134_:
{
lean_object* v___x_4138_; 
if (v_isShared_4136_ == 0)
{
lean_ctor_set(v___x_4135_, 0, v_a_4131_);
v___x_4138_ = v___x_4135_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4131_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
return v___x_4138_;
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_a_4131_);
v_a_4142_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4133_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4133_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
else
{
lean_dec_ref(v_e_4114_);
return v___x_4130_;
}
}
else
{
lean_object* v_val_4150_; lean_object* v___x_4152_; 
lean_dec_ref(v_e_4114_);
lean_dec_ref(v_post_4113_);
lean_dec_ref(v_pre_4112_);
v_val_4150_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_val_4150_);
lean_dec_ref_known(v___x_4127_, 1);
if (v_isShared_4126_ == 0)
{
lean_ctor_set(v___x_4125_, 0, v_val_4150_);
v___x_4152_ = v___x_4125_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_val_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v_e_4114_);
lean_dec_ref(v_post_4113_);
lean_dec_ref(v_pre_4112_);
v_a_4155_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4122_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4122_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_4112_ = stack[0].m_obj;
lean_object* v_post_4113_ = stack[1].m_obj;
lean_object* v_e_4114_ = stack[2].m_obj;
lean_object* v_a_4115_ = stack[3].m_obj;
lean_object* v___y_4116_ = stack[4].m_obj;
lean_object* v___y_4117_ = stack[5].m_obj;
lean_object* v___y_4118_ = stack[6].m_obj;
lean_object* v___y_4119_ = stack[7].m_obj;
lean_object* v_res_4163_;
v_res_4163_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4112_, v_post_4113_, v_e_4114_, v_a_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
stack->m_obj
 = v_res_4163_;
}
lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_4164_, lean_object* v_post_4165_, lean_object* v_e_4166_, lean_object* v_a_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
lean_inc_ref(v_post_4165_);
lean_inc(v___y_4171_);
lean_inc_ref(v___y_4170_);
lean_inc(v___y_4169_);
lean_inc_ref(v___y_4168_);
lean_inc_ref(v_e_4166_);
v___x_4173_ = lean_apply_6(v_post_4165_, v_e_4166_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, lean_box(0));
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4192_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4192_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4192_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
switch(lean_obj_tag(v_a_4174_))
{
case 0:
{
lean_object* v_e_4178_; lean_object* v___x_4180_; 
lean_dec_ref(v_e_4166_);
lean_dec_ref(v_post_4165_);
lean_dec_ref(v_pre_4164_);
v_e_4178_ = lean_ctor_get(v_a_4174_, 0);
lean_inc_ref(v_e_4178_);
lean_dec_ref_known(v_a_4174_, 1);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v_e_4178_);
v___x_4180_ = v___x_4176_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_e_4178_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
case 1:
{
lean_object* v_e_4182_; lean_object* v___x_4183_; 
lean_del_object(v___x_4176_);
lean_dec_ref(v_e_4166_);
v_e_4182_ = lean_ctor_get(v_a_4174_, 0);
lean_inc_ref(v_e_4182_);
lean_dec_ref_known(v_a_4174_, 1);
v___x_4183_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4164_, v_post_4165_, v_e_4182_, v_a_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4183_;
}
default: 
{
lean_object* v_e_x3f_4184_; 
lean_dec_ref(v_post_4165_);
lean_dec_ref(v_pre_4164_);
v_e_x3f_4184_ = lean_ctor_get(v_a_4174_, 0);
lean_inc(v_e_x3f_4184_);
lean_dec_ref_known(v_a_4174_, 1);
if (lean_obj_tag(v_e_x3f_4184_) == 0)
{
lean_object* v___x_4186_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v_e_4166_);
v___x_4186_ = v___x_4176_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_e_4166_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
else
{
lean_object* v_val_4188_; lean_object* v___x_4190_; 
lean_dec_ref(v_e_4166_);
v_val_4188_ = lean_ctor_get(v_e_x3f_4184_, 0);
lean_inc(v_val_4188_);
lean_dec_ref_known(v_e_x3f_4184_, 1);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v_val_4188_);
v___x_4190_ = v___x_4176_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_val_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
}
else
{
lean_object* v_a_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
lean_dec_ref(v_e_4166_);
lean_dec_ref(v_post_4165_);
lean_dec_ref(v_pre_4164_);
v_a_4193_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4173_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_a_4193_);
lean_dec(v___x_4173_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_a_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_4164_ = stack[0].m_obj;
lean_object* v_post_4165_ = stack[1].m_obj;
lean_object* v_e_4166_ = stack[2].m_obj;
lean_object* v_a_4167_ = stack[3].m_obj;
lean_object* v___y_4168_ = stack[4].m_obj;
lean_object* v___y_4169_ = stack[5].m_obj;
lean_object* v___y_4170_ = stack[6].m_obj;
lean_object* v___y_4171_ = stack[7].m_obj;
lean_object* v_res_4201_;
v_res_4201_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4164_, v_post_4165_, v_e_4166_, v_a_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
stack->m_obj
 = v_res_4201_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4202_, lean_object* v_post_4203_, lean_object* v_e_4204_, lean_object* v_a_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4202_, v_post_4203_, v_e_4204_, v_a_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v_a_4205_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6___boxed(lean_object* v_pre_4212_, lean_object* v_post_4213_, lean_object* v_sz_4214_, lean_object* v_i_4215_, lean_object* v_bs_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
size_t v_sz_boxed_4223_; size_t v_i_boxed_4224_; lean_object* v_res_4225_; 
v_sz_boxed_4223_ = lean_unbox_usize(v_sz_4214_);
lean_dec(v_sz_4214_);
v_i_boxed_4224_ = lean_unbox_usize(v_i_4215_);
lean_dec(v_i_4215_);
v_res_4225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_4212_, v_post_4213_, v_sz_boxed_4223_, v_i_boxed_4224_, v_bs_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4226_, lean_object* v_post_4227_, lean_object* v_x_4228_, lean_object* v_x_4229_, lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v_res_4237_; 
v_res_4237_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4226_, v_post_4227_, v_x_4228_, v_x_4229_, v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
return v_res_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object* v_pre_4238_, lean_object* v_post_4239_, lean_object* v_e_4240_, lean_object* v_a_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4238_, v_post_4239_, v_e_4240_, v_a_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v_a_4241_);
return v_res_4247_;
}
}
lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object* v_input_4248_, lean_object* v_pre_4249_, lean_object* v_post_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v_a_4258_; lean_object* v___x_4259_; 
v___x_4256_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_4257_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4256_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref(v___x_4257_);
v___x_4259_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4249_, v_post_4250_, v_input_4248_, v_a_4258_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4261_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4261_, 0, lean_box(0));
lean_closure_set(v___x_4261_, 1, lean_box(0));
lean_closure_set(v___x_4261_, 2, v_a_4258_);
v___x_4262_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4261_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4269_ == 0)
{
lean_object* v_unused_4270_; 
v_unused_4270_ = lean_ctor_get(v___x_4262_, 0);
lean_dec(v_unused_4270_);
v___x_4264_ = v___x_4262_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_dec(v___x_4262_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v_a_4260_);
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4260_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
else
{
lean_dec(v_a_4258_);
return v___x_4259_;
}
}
}
LEAN_EXPORT void l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_4248_ = stack[0].m_obj;
lean_object* v_pre_4249_ = stack[1].m_obj;
lean_object* v_post_4250_ = stack[2].m_obj;
lean_object* v___y_4251_ = stack[3].m_obj;
lean_object* v___y_4252_ = stack[4].m_obj;
lean_object* v___y_4253_ = stack[5].m_obj;
lean_object* v___y_4254_ = stack[6].m_obj;
lean_object* v_res_4271_;
v_res_4271_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4248_, v_pre_4249_, v_post_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
stack->m_obj
 = v_res_4271_;
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object* v_input_4272_, lean_object* v_pre_4273_, lean_object* v_post_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4272_, v_pre_4273_, v_post_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
return v_res_4280_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4281_; double v___x_4282_; 
v___x_4281_ = lean_unsigned_to_nat(0u);
v___x_4282_ = lean_float_of_nat(v___x_4281_);
return v___x_4282_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_4286_, lean_object* v_msg_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_ref_4293_; lean_object* v___x_4294_; lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4340_; 
v_ref_4293_ = lean_ctor_get(v___y_4290_, 2);
v___x_4294_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4340_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4340_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; lean_object* v_traceState_4300_; lean_object* v_env_4301_; lean_object* v_nextMacroScope_4302_; lean_object* v_ngen_4303_; lean_object* v_auxDeclNGen_4304_; lean_object* v_cache_4305_; lean_object* v_recordedDeps_4306_; lean_object* v_messages_4307_; lean_object* v_infoState_4308_; lean_object* v_snapshotTasks_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4339_; 
v___x_4299_ = lean_st_ref_take(v___y_4291_);
v_traceState_4300_ = lean_ctor_get(v___x_4299_, 4);
v_env_4301_ = lean_ctor_get(v___x_4299_, 0);
v_nextMacroScope_4302_ = lean_ctor_get(v___x_4299_, 1);
v_ngen_4303_ = lean_ctor_get(v___x_4299_, 2);
v_auxDeclNGen_4304_ = lean_ctor_get(v___x_4299_, 3);
v_cache_4305_ = lean_ctor_get(v___x_4299_, 5);
v_recordedDeps_4306_ = lean_ctor_get(v___x_4299_, 6);
v_messages_4307_ = lean_ctor_get(v___x_4299_, 7);
v_infoState_4308_ = lean_ctor_get(v___x_4299_, 8);
v_snapshotTasks_4309_ = lean_ctor_get(v___x_4299_, 9);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4311_ = v___x_4299_;
v_isShared_4312_ = v_isSharedCheck_4339_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_snapshotTasks_4309_);
lean_inc(v_infoState_4308_);
lean_inc(v_messages_4307_);
lean_inc(v_recordedDeps_4306_);
lean_inc(v_cache_4305_);
lean_inc(v_traceState_4300_);
lean_inc(v_auxDeclNGen_4304_);
lean_inc(v_ngen_4303_);
lean_inc(v_nextMacroScope_4302_);
lean_inc(v_env_4301_);
lean_dec(v___x_4299_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4339_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
uint64_t v_tid_4313_; lean_object* v_traces_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4338_; 
v_tid_4313_ = lean_ctor_get_uint64(v_traceState_4300_, sizeof(void*)*1);
v_traces_4314_ = lean_ctor_get(v_traceState_4300_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_traceState_4300_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4316_ = v_traceState_4300_;
v_isShared_4317_ = v_isSharedCheck_4338_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_traces_4314_);
lean_dec(v_traceState_4300_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4338_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v___x_4318_; lean_object* v___x_4319_; double v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4329_; 
v___x_4318_ = lean_box(0);
v___x_4319_ = lean_box(0);
v___x_4320_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0);
v___x_4321_ = 0;
v___x_4322_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1));
v___x_4323_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4323_, 0, v_cls_4286_);
lean_ctor_set(v___x_4323_, 1, v___x_4319_);
lean_ctor_set(v___x_4323_, 2, v___x_4322_);
lean_ctor_set_float(v___x_4323_, sizeof(void*)*3, v___x_4320_);
lean_ctor_set_float(v___x_4323_, sizeof(void*)*3 + 8, v___x_4320_);
lean_ctor_set_uint8(v___x_4323_, sizeof(void*)*3 + 16, v___x_4321_);
v___x_4324_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2));
v___x_4325_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4323_);
lean_ctor_set(v___x_4325_, 1, v_a_4295_);
lean_ctor_set(v___x_4325_, 2, v___x_4324_);
lean_inc(v_ref_4293_);
v___x_4326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4326_, 0, v_ref_4293_);
lean_ctor_set(v___x_4326_, 1, v___x_4325_);
v___x_4327_ = l_Lean_PersistentArray_push___redArg(v_traces_4314_, v___x_4326_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v___x_4327_);
v___x_4329_ = v___x_4316_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4327_);
lean_ctor_set_uint64(v_reuseFailAlloc_4337_, sizeof(void*)*1, v_tid_4313_);
v___x_4329_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
lean_object* v___x_4331_; 
if (v_isShared_4312_ == 0)
{
lean_ctor_set(v___x_4311_, 4, v___x_4329_);
v___x_4331_ = v___x_4311_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_env_4301_);
lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_nextMacroScope_4302_);
lean_ctor_set(v_reuseFailAlloc_4336_, 2, v_ngen_4303_);
lean_ctor_set(v_reuseFailAlloc_4336_, 3, v_auxDeclNGen_4304_);
lean_ctor_set(v_reuseFailAlloc_4336_, 4, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4336_, 5, v_cache_4305_);
lean_ctor_set(v_reuseFailAlloc_4336_, 6, v_recordedDeps_4306_);
lean_ctor_set(v_reuseFailAlloc_4336_, 7, v_messages_4307_);
lean_ctor_set(v_reuseFailAlloc_4336_, 8, v_infoState_4308_);
lean_ctor_set(v_reuseFailAlloc_4336_, 9, v_snapshotTasks_4309_);
v___x_4331_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
lean_object* v___x_4332_; lean_object* v___x_4334_; 
v___x_4332_ = lean_st_ref_put(v___y_4291_, v___x_4331_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4318_);
v___x_4334_ = v___x_4297_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v___x_4318_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
return v___x_4334_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_4286_ = stack[0].m_obj;
lean_object* v_msg_4287_ = stack[1].m_obj;
lean_object* v___y_4288_ = stack[2].m_obj;
lean_object* v___y_4289_ = stack[3].m_obj;
lean_object* v___y_4290_ = stack[4].m_obj;
lean_object* v___y_4291_ = stack[5].m_obj;
lean_object* v_res_4341_;
v_res_4341_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_4286_, v_msg_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
stack->m_obj
 = v_res_4341_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_4342_, lean_object* v_msg_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v_res_4349_; 
v_res_4349_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_4342_, v_msg_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
return v_res_4349_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4350_, size_t v_i_4351_, lean_object* v_bs_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
uint8_t v___x_4358_; 
v___x_4358_ = lean_usize_dec_lt(v_i_4351_, v_sz_4350_);
if (v___x_4358_ == 0)
{
lean_object* v___x_4359_; 
v___x_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4359_, 0, v_bs_4352_);
return v___x_4359_;
}
else
{
lean_object* v_v_4360_; lean_object* v___x_4361_; lean_object* v_bs_x27_4362_; lean_object* v___x_4363_; 
v_v_4360_ = lean_array_uget(v_bs_4352_, v_i_4351_);
v___x_4361_ = lean_unsigned_to_nat(0u);
v_bs_x27_4362_ = lean_array_uset(v_bs_4352_, v_i_4351_, v___x_4361_);
v___x_4363_ = l_Lean_Elab_WF_mkWfParam(v_v_4360_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; size_t v___x_4365_; size_t v___x_4366_; lean_object* v___x_4367_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
v___x_4365_ = ((size_t)1ULL);
v___x_4366_ = lean_usize_add(v_i_4351_, v___x_4365_);
v___x_4367_ = lean_array_uset(v_bs_x27_4362_, v_i_4351_, v_a_4364_);
v_i_4351_ = v___x_4366_;
v_bs_4352_ = v___x_4367_;
goto _start;
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_dec_ref(v_bs_x27_4362_);
v_a_4369_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4363_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4363_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_4350_ = stack[0].m_num;
size_t v_i_4351_ = stack[1].m_num;
lean_object* v_bs_4352_ = stack[2].m_obj;
lean_object* v___y_4353_ = stack[3].m_obj;
lean_object* v___y_4354_ = stack[4].m_obj;
lean_object* v___y_4355_ = stack[5].m_obj;
lean_object* v___y_4356_ = stack[6].m_obj;
lean_object* v_res_4377_;
v_res_4377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4350_, v_i_4351_, v_bs_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
stack->m_obj
 = v_res_4377_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4378_, lean_object* v_i_4379_, lean_object* v_bs_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
size_t v_sz_boxed_4386_; size_t v_i_boxed_4387_; lean_object* v_res_4388_; 
v_sz_boxed_4386_ = lean_unbox_usize(v_sz_4378_);
lean_dec(v_sz_4378_);
v_i_boxed_4387_ = lean_unbox_usize(v_i_4379_);
lean_dec(v_i_4379_);
v_res_4388_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4386_, v_i_boxed_4387_, v_bs_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
return v_res_4388_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4389_; 
v___x_4389_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_4389_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4390_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_4391_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__0, &l_Lean_Elab_WF_preprocess___lam__2___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0);
v___x_4392_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4391_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
lean_ctor_set(v___x_4392_, 2, v___x_4390_);
lean_ctor_set(v___x_4392_, 3, v___x_4390_);
return v___x_4392_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_4394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4394_, 0, v___x_4393_);
return v___x_4394_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3(void){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4395_ = lean_unsigned_to_nat(0u);
v___x_4396_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
lean_ctor_set(v___x_4397_, 1, v___x_4395_);
return v___x_4397_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4(void){
_start:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_unsigned_to_nat(32u);
v___x_4399_ = lean_mk_empty_array_with_capacity(v___x_4398_);
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v___x_4399_);
return v___x_4400_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5(void){
_start:
{
size_t v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4401_ = ((size_t)5ULL);
v___x_4402_ = lean_unsigned_to_nat(0u);
v___x_4403_ = lean_unsigned_to_nat(32u);
v___x_4404_ = lean_mk_empty_array_with_capacity(v___x_4403_);
v___x_4405_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4406_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
lean_ctor_set(v___x_4406_, 1, v___x_4404_);
lean_ctor_set(v___x_4406_, 2, v___x_4402_);
lean_ctor_set(v___x_4406_, 3, v___x_4402_);
lean_ctor_set_usize(v___x_4406_, 4, v___x_4401_);
return v___x_4406_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6(void){
_start:
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4407_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__5, &l_Lean_Elab_WF_preprocess___lam__2___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5);
v___x_4408_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4408_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
lean_ctor_set(v___x_4409_, 2, v___x_4408_);
lean_ctor_set(v___x_4409_, 3, v___x_4407_);
return v___x_4409_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7(void){
_start:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4410_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__6, &l_Lean_Elab_WF_preprocess___lam__2___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6);
v___x_4411_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__3, &l_Lean_Elab_WF_preprocess___lam__2___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3);
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4411_);
lean_ctor_set(v___x_4412_, 1, v___x_4410_);
return v___x_4412_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__12(void){
_start:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4421_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__9));
v___x_4422_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4423_ = l_Lean_Name_append(v___x_4422_, v___x_4421_);
return v___x_4423_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__13));
v___x_4426_ = l_Lean_stringToMessageData(v___x_4425_);
return v___x_4426_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16(void){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4428_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__15));
v___x_4429_ = l_Lean_stringToMessageData(v___x_4428_);
return v___x_4429_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__17));
v___x_4432_ = l_Lean_stringToMessageData(v___x_4431_);
return v___x_4432_;
}
}
lean_object* l_Lean_Elab_WF_preprocess___lam__2(lean_object* v_a_4433_, uint8_t v___x_4434_, lean_object* v___f_4435_, lean_object* v___f_4436_, lean_object* v_xs_4437_, lean_object* v_x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
size_t v_sz_4444_; size_t v___x_4445_; lean_object* v___x_4446_; 
v_sz_4444_ = lean_array_size(v_xs_4437_);
v___x_4445_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4437_);
v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4444_, v___x_4445_, v_xs_4437_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
v___x_4448_ = l_Lean_Expr_beta(v_a_4433_, v_a_4447_);
v___x_4449_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__1, &l_Lean_Elab_WF_preprocess___lam__2___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1);
v___x_4450_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_4451_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4449_, v___x_4450_, v___x_4434_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; uint8_t v___x_4454_; lean_object* v___x_4455_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v___x_4453_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_));
v___x_4454_ = 0;
v___x_4455_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4452_, v___x_4453_, v___x_4454_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v_a_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_a_4456_);
lean_dec_ref_known(v___x_4455_, 1);
v___x_4457_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_));
v___x_4458_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4456_, v___x_4457_, v___x_4434_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___x_4460_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4458_, 1);
v___x_4460_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4439_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4460_, 1);
v___x_4462_ = lean_unsigned_to_nat(1u);
v___x_4463_ = lean_mk_empty_array_with_capacity(v___x_4462_);
v___x_4464_ = lean_array_push(v___x_4463_, v_a_4459_);
v___x_4465_ = lean_box(0);
v___x_4466_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__7, &l_Lean_Elab_WF_preprocess___lam__2___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7);
lean_inc_ref(v___x_4448_);
v___x_4467_ = l_Lean_Meta_simp(v___x_4448_, v_a_4461_, v___x_4464_, v___x_4465_, v___x_4466_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v_fst_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4538_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref_known(v___x_4467_, 1);
v_fst_4469_ = lean_ctor_get(v_a_4468_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_a_4468_);
if (v_isSharedCheck_4538_ == 0)
{
lean_object* v_unused_4539_; 
v_unused_4539_ = lean_ctor_get(v_a_4468_, 1);
lean_dec(v_unused_4539_);
v___x_4471_ = v_a_4468_;
v_isShared_4472_ = v_isSharedCheck_4538_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_fst_4469_);
lean_dec(v_a_4468_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4538_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v_expr_4473_; lean_object* v_proof_x3f_4474_; uint8_t v_cache_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4537_; 
v_expr_4473_ = lean_ctor_get(v_fst_4469_, 0);
v_proof_x3f_4474_ = lean_ctor_get(v_fst_4469_, 1);
v_cache_4475_ = lean_ctor_get_uint8(v_fst_4469_, sizeof(void*)*2);
v_isSharedCheck_4537_ = !lean_is_exclusive(v_fst_4469_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4477_ = v_fst_4469_;
v_isShared_4478_ = v_isSharedCheck_4537_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_proof_x3f_4474_);
lean_inc(v_expr_4473_);
lean_dec(v_fst_4469_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4537_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4479_; 
lean_inc_ref(v_expr_4473_);
v___x_4479_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4473_, v___f_4435_, v___f_4436_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4481_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4479_, 1);
v___x_4481_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4480_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v_toCold_4492_; lean_object* v_options_4493_; uint8_t v_hasTrace_4494_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v_toCold_4492_ = lean_ctor_get(v___y_4441_, 0);
v_options_4493_ = lean_ctor_get(v_toCold_4492_, 2);
v_hasTrace_4494_ = lean_ctor_get_uint8(v_options_4493_, sizeof(void*)*1);
if (v_hasTrace_4494_ == 0)
{
lean_dec_ref(v_expr_4473_);
lean_del_object(v___x_4471_);
lean_dec_ref(v___x_4448_);
v___y_4484_ = v___y_4439_;
v___y_4485_ = v___y_4440_;
v___y_4486_ = v___y_4441_;
v___y_4487_ = v___y_4442_;
goto v___jp_4483_;
}
else
{
lean_object* v_inheritedTraceOptions_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; uint8_t v___x_4498_; 
v_inheritedTraceOptions_4495_ = lean_ctor_get(v_toCold_4492_, 11);
v___x_4496_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__9));
v___x_4497_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__12, &l_Lean_Elab_WF_preprocess___lam__2___closed__12_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__12);
v___x_4498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4495_, v_options_4493_, v___x_4497_);
if (v___x_4498_ == 0)
{
lean_dec_ref(v_expr_4473_);
lean_del_object(v___x_4471_);
lean_dec_ref(v___x_4448_);
v___y_4484_ = v___y_4439_;
v___y_4485_ = v___y_4440_;
v___y_4486_ = v___y_4441_;
v___y_4487_ = v___y_4442_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4499_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__14, &l_Lean_Elab_WF_preprocess___lam__2___closed__14_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14);
v___x_4500_ = l_Lean_indentExpr(v___x_4448_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set_tag(v___x_4471_, 7);
lean_ctor_set(v___x_4471_, 1, v___x_4500_);
lean_ctor_set(v___x_4471_, 0, v___x_4499_);
v___x_4502_ = v___x_4471_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4499_);
lean_ctor_set(v_reuseFailAlloc_4520_, 1, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4503_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__16, &l_Lean_Elab_WF_preprocess___lam__2___closed__16_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16);
v___x_4504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4504_, 0, v___x_4502_);
lean_ctor_set(v___x_4504_, 1, v___x_4503_);
v___x_4505_ = l_Lean_indentExpr(v_expr_4473_);
v___x_4506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4504_);
lean_ctor_set(v___x_4506_, 1, v___x_4505_);
v___x_4507_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__18, &l_Lean_Elab_WF_preprocess___lam__2___closed__18_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18);
v___x_4508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
lean_inc(v_a_4482_);
v___x_4509_ = l_Lean_indentExpr(v_a_4482_);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v___x_4496_, v___x_4510_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_dec_ref_known(v___x_4511_, 1);
v___y_4484_ = v___y_4439_;
v___y_4485_ = v___y_4440_;
v___y_4486_ = v___y_4441_;
v___y_4487_ = v___y_4442_;
goto v___jp_4483_;
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_dec(v_a_4482_);
lean_del_object(v___x_4477_);
lean_dec(v_proof_x3f_4474_);
lean_dec_ref(v_xs_4437_);
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4511_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4511_);
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
}
}
v___jp_4483_:
{
lean_object* v___x_4489_; 
if (v_isShared_4478_ == 0)
{
lean_ctor_set(v___x_4477_, 0, v_a_4482_);
v___x_4489_ = v___x_4477_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4482_);
lean_ctor_set(v_reuseFailAlloc_4491_, 1, v_proof_x3f_4474_);
lean_ctor_set_uint8(v_reuseFailAlloc_4491_, sizeof(void*)*2, v_cache_4475_);
v___x_4489_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4489_, v_xs_4437_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
lean_dec_ref(v_xs_4437_);
return v___x_4490_;
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_del_object(v___x_4477_);
lean_dec(v_proof_x3f_4474_);
lean_dec_ref(v_expr_4473_);
lean_del_object(v___x_4471_);
lean_dec_ref(v___x_4448_);
lean_dec_ref(v_xs_4437_);
v_a_4521_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4481_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4481_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_del_object(v___x_4477_);
lean_dec(v_proof_x3f_4474_);
lean_dec_ref(v_expr_4473_);
lean_del_object(v___x_4471_);
lean_dec_ref(v___x_4448_);
lean_dec_ref(v_xs_4437_);
v_a_4529_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4479_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4479_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
}
else
{
lean_object* v_a_4540_; lean_object* v___x_4542_; uint8_t v_isShared_4543_; uint8_t v_isSharedCheck_4547_; 
lean_dec_ref(v___x_4448_);
lean_dec_ref(v_xs_4437_);
lean_dec_ref(v___f_4436_);
lean_dec_ref(v___f_4435_);
v_a_4540_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4547_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4547_ == 0)
{
v___x_4542_ = v___x_4467_;
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
else
{
lean_inc(v_a_4540_);
lean_dec(v___x_4467_);
v___x_4542_ = lean_box(0);
v_isShared_4543_ = v_isSharedCheck_4547_;
goto v_resetjp_4541_;
}
v_resetjp_4541_:
{
lean_object* v___x_4545_; 
if (v_isShared_4543_ == 0)
{
v___x_4545_ = v___x_4542_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v_a_4540_);
v___x_4545_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
return v___x_4545_;
}
}
}
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
lean_dec(v_a_4459_);
lean_dec_ref(v___x_4448_);
lean_dec_ref(v_xs_4437_);
lean_dec_ref(v___f_4436_);
lean_dec_ref(v___f_4435_);
v_a_4548_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___x_4460_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___x_4460_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec_ref(v___x_4448_);
lean_dec_ref(v_xs_4437_);
lean_dec_ref(v___f_4436_);
lean_dec_ref(v___f_4435_);
v_a_4556_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4458_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4458_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
}
else
{
lean_object* v_a_4564_; lean_object* v___x_4566_; uint8_t v_isShared_4567_; uint8_t v_isSharedCheck_4571_; 
lean_dec_ref(v___x_4448_);
lean_dec_ref(v_xs_4437_);
lean_dec_ref(v___f_4436_);
lean_dec_ref(v___f_4435_);
v_a_4564_ = lean_ctor_get(v___x_4455_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4455_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4566_ = v___x_4455_;
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
else
{
lean_inc(v_a_4564_);
lean_dec(v___x_4455_);
v___x_4566_ = lean_box(0);
v_isShared_4567_ = v_isSharedCheck_4571_;
goto v_resetjp_4565_;
}
v_resetjp_4565_:
{
lean_object* v___x_4569_; 
if (v_isShared_4567_ == 0)
{
v___x_4569_ = v___x_4566_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4564_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v___x_4448_);
lean_dec_ref(v_xs_4437_);
lean_dec_ref(v___f_4436_);
lean_dec_ref(v___f_4435_);
v_a_4572_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4451_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4451_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec_ref(v_xs_4437_);
lean_dec_ref(v___f_4436_);
lean_dec_ref(v___f_4435_);
lean_dec_ref(v_a_4433_);
v_a_4580_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4446_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4446_);
v___x_4582_ = lean_box(0);
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
v_resetjp_4581_:
{
lean_object* v___x_4585_; 
if (v_isShared_4583_ == 0)
{
v___x_4585_ = v___x_4582_;
goto v_reusejp_4584_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v_a_4580_);
v___x_4585_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4584_;
}
v_reusejp_4584_:
{
return v___x_4585_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_preprocess___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4433_ = stack[0].m_obj;
uint8_t v___x_4434_ = stack[1].m_num;
lean_object* v___f_4435_ = stack[2].m_obj;
lean_object* v___f_4436_ = stack[3].m_obj;
lean_object* v_xs_4437_ = stack[4].m_obj;
lean_object* v_x_4438_ = stack[5].m_obj;
lean_object* v___y_4439_ = stack[6].m_obj;
lean_object* v___y_4440_ = stack[7].m_obj;
lean_object* v___y_4441_ = stack[8].m_obj;
lean_object* v___y_4442_ = stack[9].m_obj;
lean_object* v_res_4588_;
v_res_4588_ = l_Lean_Elab_WF_preprocess___lam__2(v_a_4433_, v___x_4434_, v___f_4435_, v___f_4436_, v_xs_4437_, v_x_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
stack->m_obj
 = v_res_4588_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2___boxed(lean_object* v_a_4589_, lean_object* v___x_4590_, lean_object* v___f_4591_, lean_object* v___f_4592_, lean_object* v_xs_4593_, lean_object* v_x_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
uint8_t v___x_14540__boxed_4600_; lean_object* v_res_4601_; 
v___x_14540__boxed_4600_ = lean_unbox(v___x_4590_);
v_res_4601_ = l_Lean_Elab_WF_preprocess___lam__2(v_a_4589_, v___x_14540__boxed_4600_, v___f_4591_, v___f_4592_, v_xs_4593_, v_x_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec_ref(v_x_4594_);
return v_res_4601_;
}
}
lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_){
_start:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; uint8_t v___x_4611_; uint8_t v___x_4612_; 
v___x_4609_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4606_);
v___x_4610_ = l_Lean_wf_preprocess;
v___x_4611_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v___x_4609_, v___x_4610_);
lean_dec_ref(v___x_4609_);
v___x_4612_ = 1;
if (v___x_4611_ == 0)
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; 
v___x_4613_ = lean_box(0);
v___x_4614_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4614_, 0, v_e_4603_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
lean_ctor_set_uint8(v___x_4614_, sizeof(void*)*2, v___x_4612_);
v___x_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4615_, 0, v___x_4614_);
return v___x_4615_;
}
else
{
lean_object* v___f_4616_; lean_object* v___f_4617_; lean_object* v___x_4618_; 
v___f_4616_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___f_4617_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___x_4618_ = l_Lean_Meta_letToHave(v_e_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v_a_4619_; lean_object* v___x_4620_; lean_object* v___f_4621_; uint8_t v___x_4622_; lean_object* v___x_4623_; 
v_a_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc_n(v_a_4619_, 2);
lean_dec_ref_known(v___x_4618_, 1);
v___x_4620_ = lean_box(v___x_4612_);
v___f_4621_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__2___boxed), 11, 4);
lean_closure_set(v___f_4621_, 0, v_a_4619_);
lean_closure_set(v___f_4621_, 1, v___x_4620_);
lean_closure_set(v___f_4621_, 2, v___f_4616_);
lean_closure_set(v___f_4621_, 3, v___f_4617_);
v___x_4622_ = 0;
v___x_4623_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_a_4619_, v___f_4621_, v___x_4622_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
return v___x_4623_;
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
v_a_4624_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4618_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4618_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_WF_preprocess_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4603_ = stack[0].m_obj;
lean_object* v_a_4604_ = stack[1].m_obj;
lean_object* v_a_4605_ = stack[2].m_obj;
lean_object* v_a_4606_ = stack[3].m_obj;
lean_object* v_a_4607_ = stack[4].m_obj;
lean_object* v_res_4632_;
v_res_4632_ = l_Lean_Elab_WF_preprocess(v_e_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_);
stack->m_obj
 = v_res_4632_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_Elab_WF_preprocess(v_e_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
return v_res_4639_;
}
}
lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4640_, lean_object* v_x_4641_, lean_object* v_x_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v___x_4648_; 
v___x_4648_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4640_, v_x_4641_, v_x_4642_);
return v___x_4648_;
}
}
LEAN_EXPORT void l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4640_ = stack[0].m_obj;
lean_object* v_x_4641_ = stack[1].m_obj;
lean_object* v_x_4642_ = stack[2].m_obj;
lean_object* v___y_4643_ = stack[3].m_obj;
lean_object* v___y_4644_ = stack[4].m_obj;
lean_object* v___y_4645_ = stack[5].m_obj;
lean_object* v___y_4646_ = stack[6].m_obj;
lean_object* v_res_4649_;
v_res_4649_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4640_, v_x_4641_, v_x_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
stack->m_obj
 = v_res_4649_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4650_, lean_object* v_x_4651_, lean_object* v_x_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4650_, v_x_4651_, v_x_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
return v_res_4658_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_4659_, lean_object* v_ref_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_4660_);
return v___x_4664_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4660_ = stack[1].m_obj;
lean_object* v___y_4661_ = stack[2].m_obj;
lean_object* v___y_4662_ = stack[3].m_obj;
lean_object* v_res_4665_;
v_res_4665_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_box(0), v_ref_4660_, v___y_4661_, v___y_4662_);
stack->m_obj
 = v_res_4665_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4666_, lean_object* v_ref_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(v_00_u03b1_4666_, v_ref_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
return v_res_4671_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(lean_object* v_00_u03b1_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v___x_4676_; 
v___x_4676_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v___x_4676_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4673_ = stack[1].m_obj;
lean_object* v___y_4674_ = stack[2].m_obj;
lean_object* v_res_4677_;
v_res_4677_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(lean_box(0), v___y_4673_, v___y_4674_);
stack->m_obj
 = v_res_4677_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(v_00_u03b1_4678_, v___y_4679_, v___y_4680_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
return v_res_4682_;
}
}
lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_00_u03b1_4683_, lean_object* v_x_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v___x_4691_; 
v___x_4691_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
return v___x_4691_;
}
}
LEAN_EXPORT void l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_4684_ = stack[1].m_obj;
lean_object* v___y_4685_ = stack[2].m_obj;
lean_object* v___y_4686_ = stack[3].m_obj;
lean_object* v___y_4687_ = stack[4].m_obj;
lean_object* v___y_4688_ = stack[5].m_obj;
lean_object* v___y_4689_ = stack[6].m_obj;
lean_object* v_res_4692_;
v_res_4692_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_box(0), v_x_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
stack->m_obj
 = v_res_4692_;
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_00_u03b1_4693_, lean_object* v_x_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_00_u03b1_4693_, v_x_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
return v_res_4701_;
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
