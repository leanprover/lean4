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
lean_object* v_toCold_481_; lean_object* v_currRecDepth_482_; lean_object* v_ref_483_; uint16_t v_optionFlags_484_; uint8_t v_suppressElabErrors_485_; uint8_t v_checkDeprecated_486_; uint8_t v_isRecordingDeps_487_; lean_object* v_ref_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_toCold_481_ = lean_ctor_get(v___y_478_, 0);
v_currRecDepth_482_ = lean_ctor_get(v___y_478_, 1);
v_ref_483_ = lean_ctor_get(v___y_478_, 2);
v_optionFlags_484_ = lean_ctor_get_uint16(v___y_478_, sizeof(void*)*3);
v_suppressElabErrors_485_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 2);
v_checkDeprecated_486_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 3);
v_isRecordingDeps_487_ = lean_ctor_get_uint8(v___y_478_, sizeof(void*)*3 + 4);
v_ref_488_ = l_Lean_replaceRef(v_ref_471_, v_ref_483_);
lean_inc(v_currRecDepth_482_);
lean_inc_ref(v_toCold_481_);
v___x_489_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_489_, 0, v_toCold_481_);
lean_ctor_set(v___x_489_, 1, v_currRecDepth_482_);
lean_ctor_set(v___x_489_, 2, v_ref_488_);
lean_ctor_set_uint16(v___x_489_, sizeof(void*)*3, v_optionFlags_484_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*3 + 2, v_suppressElabErrors_485_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*3 + 3, v_checkDeprecated_486_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*3 + 4, v_isRecordingDeps_487_);
v___x_490_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_472_, v___y_476_, v___y_477_, v___x_489_, v___y_479_);
lean_dec_ref_known(v___x_489_, 3);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_491_, lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_491_, v_msg_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec(v_ref_491_);
return v_res_501_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
lean_ctor_set(v___x_507_, 3, v___x_506_);
lean_ctor_set(v___x_507_, 4, v___x_505_);
lean_ctor_set(v___x_507_, 5, v___x_505_);
lean_ctor_set(v___x_507_, 6, v___x_505_);
lean_ctor_set(v___x_507_, 7, v___x_505_);
lean_ctor_set(v___x_507_, 8, v___x_505_);
lean_ctor_set(v___x_507_, 9, v___x_505_);
lean_ctor_set(v___x_507_, 10, v___x_505_);
lean_ctor_set(v___x_507_, 11, v___x_504_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_unsigned_to_nat(32u);
v___x_509_ = lean_mk_empty_array_with_capacity(v___x_508_);
v___x_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
size_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_511_ = ((size_t)5ULL);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_unsigned_to_nat(32u);
v___x_514_ = lean_mk_empty_array_with_capacity(v___x_513_);
v___x_515_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_516_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
lean_ctor_set(v___x_516_, 2, v___x_512_);
lean_ctor_set(v___x_516_, 3, v___x_512_);
lean_ctor_set_usize(v___x_516_, 4, v___x_511_);
return v___x_516_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_517_ = lean_box(1);
v___x_518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v___x_518_);
lean_ctor_set(v___x_520_, 2, v___x_517_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5));
v___x_523_ = l_Lean_stringToMessageData(v___x_522_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7));
v___x_526_ = l_Lean_stringToMessageData(v___x_525_);
return v___x_526_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_528_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9));
v___x_529_ = l_Lean_stringToMessageData(v___x_528_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11));
v___x_532_ = l_Lean_stringToMessageData(v___x_531_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15));
v___x_538_ = l_Lean_stringToMessageData(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17));
v___x_541_ = l_Lean_stringToMessageData(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_542_, lean_object* v_declHint_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v_env_548_; uint8_t v___x_549_; 
v___x_546_ = lean_box(0);
v___x_547_ = lean_st_ref_get(v___y_544_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_547_);
v___x_549_ = l_Lean_Name_isAnonymous(v_declHint_543_);
if (v___x_549_ == 0)
{
uint8_t v_isExporting_550_; 
v_isExporting_550_ = lean_ctor_get_uint8(v_env_548_, sizeof(void*)*13);
if (v_isExporting_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec_ref(v_env_548_);
lean_dec(v_declHint_543_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_msg_542_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
lean_inc_ref(v_env_548_);
v___x_552_ = l_Lean_Environment_setExporting(v_env_548_, v___x_549_);
lean_inc(v_declHint_543_);
lean_inc_ref(v___x_552_);
v___x_553_ = l_Lean_Environment_contains(v___x_552_, v_declHint_543_, v_isExporting_550_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_dec_ref(v___x_552_);
lean_dec_ref(v_env_548_);
lean_dec(v_declHint_543_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_msg_542_);
return v___x_554_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v_c_560_; lean_object* v___x_561_; 
v___x_555_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_556_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_557_ = l_Lean_Options_empty;
lean_inc_ref(v___x_552_);
v___x_558_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_558_, 0, v___x_552_);
lean_ctor_set(v___x_558_, 1, v___x_555_);
lean_ctor_set(v___x_558_, 2, v___x_556_);
lean_ctor_set(v___x_558_, 3, v___x_557_);
lean_inc(v_declHint_543_);
v___x_559_ = l_Lean_MessageData_ofConstName(v_declHint_543_, v___x_549_);
v_c_560_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_560_, 0, v___x_558_);
lean_ctor_set(v_c_560_, 1, v___x_559_);
v___x_561_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_552_, v_declHint_543_);
lean_dec_ref(v___x_552_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v_env_548_);
lean_dec(v_declHint_543_);
v___x_562_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_c_560_);
v___x_564_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8);
v___x_565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_563_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = l_Lean_MessageData_note(v___x_565_);
v___x_567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_567_, 0, v_msg_542_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
else
{
lean_object* v_val_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_603_; 
v_val_569_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_603_ == 0)
{
v___x_571_ = v___x_561_;
v_isShared_572_ = v_isSharedCheck_603_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_val_569_);
lean_dec(v___x_561_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_603_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v_moduleNames_574_; lean_object* v_mod_575_; uint8_t v___x_576_; 
v___x_573_ = l_Lean_Environment_header(v_env_548_);
lean_dec_ref(v_env_548_);
v_moduleNames_574_ = lean_ctor_get(v___x_573_, 4);
lean_inc_ref(v_moduleNames_574_);
lean_dec_ref(v___x_573_);
v_mod_575_ = lean_array_get(v___x_546_, v_moduleNames_574_, v_val_569_);
lean_dec(v_val_569_);
lean_dec_ref(v_moduleNames_574_);
v___x_576_ = l_Lean_isPrivateName(v_declHint_543_);
lean_dec(v_declHint_543_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_577_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_c_560_);
v___x_579_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12);
v___x_580_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_578_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = l_Lean_MessageData_ofName(v_mod_575_);
v___x_582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_580_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v___x_583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14);
v___x_584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
v___x_585_ = l_Lean_MessageData_note(v___x_584_);
v___x_586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_586_, 0, v_msg_542_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 0);
lean_ctor_set(v___x_571_, 0, v___x_586_);
v___x_588_ = v___x_571_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_590_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v_c_560_);
v___x_592_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_MessageData_ofName(v_mod_575_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = l_Lean_MessageData_note(v___x_597_);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v_msg_542_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
if (v_isShared_572_ == 0)
{
lean_ctor_set_tag(v___x_571_, 0);
lean_ctor_set(v___x_571_, 0, v___x_599_);
v___x_601_ = v___x_571_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_604_; 
lean_dec_ref(v_env_548_);
lean_dec(v_declHint_543_);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v_msg_542_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_605_, lean_object* v_declHint_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_605_, v_declHint_606_, v___y_607_);
lean_dec(v___y_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object* v_msg_610_, lean_object* v_declHint_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_630_; 
v___x_620_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_610_, v_declHint_611_, v___y_618_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_630_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_625_ = l_Lean_unknownIdentifierMessageTag;
v___x_626_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_a_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_631_, lean_object* v_declHint_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_631_, v_declHint_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_ref_642_, lean_object* v_msg_643_, lean_object* v_declHint_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; lean_object* v_a_654_; lean_object* v___x_655_; 
v___x_653_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_643_, v_declHint_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref(v___x_653_);
v___x_655_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_642_, v_a_654_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_ref_656_, lean_object* v_msg_657_, lean_object* v_declHint_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_656_, v_msg_657_, v_declHint_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec(v_ref_656_);
return v_res_667_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0));
v___x_670_ = l_Lean_stringToMessageData(v___x_669_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_ref_674_, lean_object* v_constName_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; uint8_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_684_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_685_ = 0;
lean_inc(v_constName_675_);
v___x_686_ = l_Lean_MessageData_ofConstName(v_constName_675_, v___x_685_);
v___x_687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_684_);
lean_ctor_set(v___x_687_, 1, v___x_686_);
v___x_688_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3);
v___x_689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v___x_690_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_674_, v___x_689_, v_constName_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_ref_691_, lean_object* v_constName_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_691_, v_constName_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec(v_ref_691_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_ref_711_; lean_object* v___x_712_; 
v_ref_711_ = lean_ctor_get(v___y_708_, 2);
v___x_712_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_711_, v_constName_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object* v_constName_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; lean_object* v_env_733_; uint8_t v___x_734_; lean_object* v___x_735_; 
v___x_732_ = lean_st_ref_get(v___y_730_);
v_env_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_ref(v_env_733_);
lean_dec(v___x_732_);
v___x_734_ = 0;
lean_inc(v_constName_723_);
v___x_735_ = l_Lean_Environment_find_x3f(v_env_733_, v_constName_723_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
return v___x_736_;
}
else
{
lean_object* v_val_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_constName_723_);
v_val_737_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_735_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_val_737_);
lean_dec(v___x_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 0);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_val_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object* v_constName_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
return v_res_754_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_instMonadEIO___redArg();
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_toApplicative_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_835_; 
v___x_769_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0);
v___x_770_ = l_StateRefT_x27_instMonad___redArg(v___x_769_);
v_toApplicative_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_770_, 1);
lean_dec(v_unused_836_);
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_835_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_toApplicative_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_835_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_toFunctor_775_; lean_object* v_toSeq_776_; lean_object* v_toSeqLeft_777_; lean_object* v_toSeqRight_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_833_; 
v_toFunctor_775_ = lean_ctor_get(v_toApplicative_771_, 0);
v_toSeq_776_ = lean_ctor_get(v_toApplicative_771_, 2);
v_toSeqLeft_777_ = lean_ctor_get(v_toApplicative_771_, 3);
v_toSeqRight_778_ = lean_ctor_get(v_toApplicative_771_, 4);
v_isSharedCheck_833_ = !lean_is_exclusive(v_toApplicative_771_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v_toApplicative_771_, 1);
lean_dec(v_unused_834_);
v___x_780_ = v_toApplicative_771_;
v_isShared_781_ = v_isSharedCheck_833_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_toSeqRight_778_);
lean_inc(v_toSeqLeft_777_);
lean_inc(v_toSeq_776_);
lean_inc(v_toFunctor_775_);
lean_dec(v_toApplicative_771_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_833_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___f_782_; lean_object* v___f_783_; lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___x_786_; lean_object* v___f_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___x_791_; 
v___f_782_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1));
v___f_783_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_775_);
v___f_784_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_784_, 0, v_toFunctor_775_);
v___f_785_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_785_, 0, v_toFunctor_775_);
v___x_786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_786_, 0, v___f_784_);
lean_ctor_set(v___x_786_, 1, v___f_785_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toSeqRight_778_);
v___f_788_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_788_, 0, v_toSeqLeft_777_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeq_776_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 4, v___f_787_);
lean_ctor_set(v___x_780_, 3, v___f_788_);
lean_ctor_set(v___x_780_, 2, v___f_789_);
lean_ctor_set(v___x_780_, 1, v___f_782_);
lean_ctor_set(v___x_780_, 0, v___x_786_);
v___x_791_ = v___x_780_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v___f_782_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v___f_789_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v___f_788_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v___f_787_);
v___x_791_ = v_reuseFailAlloc_832_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_793_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v___f_783_);
lean_ctor_set(v___x_773_, 0, v___x_791_);
v___x_793_ = v___x_773_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___f_783_);
v___x_793_ = v_reuseFailAlloc_831_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v_toApplicative_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_829_; 
v___x_794_ = l_StateRefT_x27_instMonad___redArg(v___x_793_);
v_toApplicative_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_829_ == 0)
{
lean_object* v_unused_830_; 
v_unused_830_ = lean_ctor_get(v___x_794_, 1);
lean_dec(v_unused_830_);
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_829_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_toApplicative_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_829_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_toFunctor_799_; lean_object* v_toSeq_800_; lean_object* v_toSeqLeft_801_; lean_object* v_toSeqRight_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_827_; 
v_toFunctor_799_ = lean_ctor_get(v_toApplicative_795_, 0);
v_toSeq_800_ = lean_ctor_get(v_toApplicative_795_, 2);
v_toSeqLeft_801_ = lean_ctor_get(v_toApplicative_795_, 3);
v_toSeqRight_802_ = lean_ctor_get(v_toApplicative_795_, 4);
v_isSharedCheck_827_ = !lean_is_exclusive(v_toApplicative_795_);
if (v_isSharedCheck_827_ == 0)
{
lean_object* v_unused_828_; 
v_unused_828_ = lean_ctor_get(v_toApplicative_795_, 1);
lean_dec(v_unused_828_);
v___x_804_ = v_toApplicative_795_;
v_isShared_805_ = v_isSharedCheck_827_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_toSeqRight_802_);
lean_inc(v_toSeqLeft_801_);
lean_inc(v_toSeq_800_);
lean_inc(v_toFunctor_799_);
lean_dec(v_toApplicative_795_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_827_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___f_806_; lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___f_813_; lean_object* v___x_815_; 
v___f_806_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3));
v___f_807_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_799_);
v___f_808_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_808_, 0, v_toFunctor_799_);
v___f_809_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_809_, 0, v_toFunctor_799_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___f_808_);
lean_ctor_set(v___x_810_, 1, v___f_809_);
v___f_811_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_811_, 0, v_toSeqRight_802_);
v___f_812_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_812_, 0, v_toSeqLeft_801_);
v___f_813_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_813_, 0, v_toSeq_800_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v___f_811_);
lean_ctor_set(v___x_804_, 3, v___f_812_);
lean_ctor_set(v___x_804_, 2, v___f_813_);
lean_ctor_set(v___x_804_, 1, v___f_806_);
lean_ctor_set(v___x_804_, 0, v___x_810_);
v___x_815_ = v___x_804_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v___f_806_);
lean_ctor_set(v_reuseFailAlloc_826_, 2, v___f_813_);
lean_ctor_set(v_reuseFailAlloc_826_, 3, v___f_812_);
lean_ctor_set(v_reuseFailAlloc_826_, 4, v___f_811_);
v___x_815_ = v_reuseFailAlloc_826_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
lean_object* v___x_817_; 
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 1, v___f_807_);
lean_ctor_set(v___x_797_, 0, v___x_815_);
v___x_817_ = v___x_797_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_825_, 1, v___f_807_);
v___x_817_ = v_reuseFailAlloc_825_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_13055__overap_823_; lean_object* v___x_824_; 
v___x_818_ = l_StateRefT_x27_instMonad___redArg(v___x_817_);
v___x_819_ = l_ReaderT_instMonad___redArg(v___x_818_);
v___x_820_ = l_ReaderT_instMonad___redArg(v___x_819_);
v___x_821_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_822_ = l_instInhabitedOfMonad___redArg(v___x_820_, v___x_821_);
v___x_13055__overap_823_ = lean_panic_fn_borrowed(v___x_822_, v_msg_760_);
lean_dec(v___x_822_);
lean_inc(v___y_767_);
lean_inc_ref(v___y_766_);
lean_inc(v___y_765_);
lean_inc_ref(v___y_764_);
lean_inc(v___y_763_);
lean_inc_ref(v___y_762_);
lean_inc(v___y_761_);
v___x_824_ = lean_apply_8(v___x_13055__overap_823_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, lean_box(0));
return v___x_824_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object* v_msg_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
return v_res_846_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2));
v___x_851_ = lean_unsigned_to_nat(53u);
v___x_852_ = lean_unsigned_to_nat(62u);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1));
v___x_854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0));
v___x_855_ = l_mkPanicMessageWithDecl(v___x_854_, v___x_853_, v___x_852_, v___x_851_, v___x_850_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t v_sz_856_, size_t v_i_857_, lean_object* v_bs_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_lt(v_i_857_, v_sz_856_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_868_, 0, v_bs_858_);
return v___x_868_;
}
else
{
lean_object* v_v_869_; lean_object* v___x_870_; lean_object* v_bs_x27_871_; lean_object* v_a_873_; lean_object* v___x_878_; 
v_v_869_ = lean_array_uget(v_bs_858_, v_i_857_);
v___x_870_ = lean_unsigned_to_nat(0u);
v_bs_x27_871_ = lean_array_uset(v_bs_858_, v_i_857_, v___x_870_);
v___x_878_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_v_869_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
if (lean_obj_tag(v_a_879_) == 6)
{
lean_object* v_val_880_; lean_object* v_numFields_881_; uint8_t v___x_882_; lean_object* v___x_883_; 
v_val_880_ = lean_ctor_get(v_a_879_, 0);
lean_inc_ref(v_val_880_);
lean_dec_ref_known(v_a_879_, 1);
v_numFields_881_ = lean_ctor_get(v_val_880_, 4);
lean_inc(v_numFields_881_);
lean_dec_ref(v_val_880_);
v___x_882_ = 0;
v___x_883_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_883_, 0, v_numFields_881_);
lean_ctor_set(v___x_883_, 1, v___x_870_);
lean_ctor_set_uint8(v___x_883_, sizeof(void*)*2, v___x_882_);
v_a_873_ = v___x_883_;
goto v___jp_872_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v_a_879_);
v___x_884_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3);
v___x_885_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v___x_884_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v_a_873_ = v_a_886_;
goto v___jp_872_;
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v_bs_x27_871_);
v_a_887_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_885_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_885_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_dec_ref(v_bs_x27_871_);
v_a_895_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_878_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_878_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
v___jp_872_:
{
size_t v___x_874_; size_t v___x_875_; lean_object* v___x_876_; 
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_857_, v___x_874_);
v___x_876_ = lean_array_uset(v_bs_x27_871_, v_i_857_, v_a_873_);
v_i_857_ = v___x_875_;
v_bs_858_ = v___x_876_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_bs_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
size_t v_sz_boxed_914_; size_t v_i_boxed_915_; lean_object* v_res_916_; 
v_sz_boxed_914_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_915_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_916_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_boxed_914_, v_i_boxed_915_, v_bs_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object* v_declName_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; lean_object* v_env_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_920_ = lean_st_ref_get(v___y_918_);
v_env_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc_ref(v_env_921_);
lean_dec(v___x_920_);
v___x_922_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_921_, v_declName_917_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object* v_declName_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_924_, v___y_925_);
lean_dec(v___y_925_);
return v_res_927_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_928_; lean_object* v_dummy_929_; 
v___x_928_ = lean_box(0);
v_dummy_929_ = l_Lean_Expr_sort___override(v___x_928_);
return v_dummy_929_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_box(0);
v___x_931_ = lean_unsigned_to_nat(16u);
v___x_932_ = lean_mk_array(v___x_931_, v___x_930_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2(void){
_start:
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_933_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object* v_e_938_, uint8_t v_alsoCasesOn_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = l_Lean_Expr_isApp(v_e_938_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
lean_dec_ref(v_e_938_);
v___x_952_ = lean_box(0);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; 
v___x_954_ = l_Lean_Expr_getAppFn(v_e_938_);
if (lean_obj_tag(v___x_954_) == 4)
{
lean_object* v_declName_955_; lean_object* v_us_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1111_; 
v_declName_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc_n(v_declName_955_, 2);
v_us_956_ = lean_ctor_get(v___x_954_, 1);
lean_inc(v_us_956_);
lean_dec_ref_known(v___x_954_, 2);
v___x_957_ = l_Lean_instInhabitedExpr;
v___x_958_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_955_, v___y_946_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_1111_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1111_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
if (lean_obj_tag(v_a_959_) == 1)
{
lean_object* v_val_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_1004_; 
v_val_963_ = lean_ctor_get(v_a_959_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v_a_959_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_965_ = v_a_959_;
v_isShared_966_ = v_isSharedCheck_1004_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_val_963_);
lean_dec(v_a_959_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_1004_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v_dummy_967_; lean_object* v_nargs_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_args_972_; lean_object* v___x_973_; lean_object* v___x_974_; uint8_t v___x_975_; 
v_dummy_967_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_968_ = l_Lean_Expr_getAppNumArgs(v_e_938_);
lean_inc(v_nargs_968_);
v___x_969_ = lean_mk_array(v_nargs_968_, v_dummy_967_);
v___x_970_ = lean_unsigned_to_nat(1u);
v___x_971_ = lean_nat_sub(v_nargs_968_, v___x_970_);
lean_dec(v_nargs_968_);
v_args_972_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_938_, v___x_969_, v___x_971_);
v___x_973_ = lean_array_get_size(v_args_972_);
v___x_974_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_963_);
v___x_975_ = lean_nat_dec_lt(v___x_973_, v___x_974_);
lean_dec(v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v_numParams_976_; lean_object* v_numDiscrs_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v_numParams_976_ = lean_ctor_get(v_val_963_, 0);
v_numDiscrs_977_ = lean_ctor_get(v_val_963_, 1);
v___x_978_ = lean_array_mk(v_us_956_);
v___x_979_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_976_);
v___x_980_ = l_Array_extract___redArg(v_args_972_, v___x_979_, v_numParams_976_);
v___x_981_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_963_);
v___x_982_ = lean_array_get(v___x_957_, v_args_972_, v___x_981_);
lean_dec(v___x_981_);
v___x_983_ = lean_nat_add(v_numParams_976_, v___x_970_);
v___x_984_ = lean_nat_add(v___x_983_, v_numDiscrs_977_);
lean_inc(v___x_984_);
lean_inc_ref_n(v_args_972_, 2);
v___x_985_ = l_Array_toSubarray___redArg(v_args_972_, v___x_983_, v___x_984_);
v___x_986_ = l_Subarray_copy___redArg(v___x_985_);
v___x_987_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_963_);
v___x_988_ = lean_nat_add(v___x_984_, v___x_987_);
lean_dec(v___x_987_);
lean_inc(v___x_988_);
v___x_989_ = l_Array_toSubarray___redArg(v_args_972_, v___x_984_, v___x_988_);
v___x_990_ = l_Subarray_copy___redArg(v___x_989_);
v___x_991_ = l_Array_toSubarray___redArg(v_args_972_, v___x_988_, v___x_973_);
v___x_992_ = l_Subarray_copy___redArg(v___x_991_);
v___x_993_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_993_, 0, v_val_963_);
lean_ctor_set(v___x_993_, 1, v_declName_955_);
lean_ctor_set(v___x_993_, 2, v___x_978_);
lean_ctor_set(v___x_993_, 3, v___x_980_);
lean_ctor_set(v___x_993_, 4, v___x_982_);
lean_ctor_set(v___x_993_, 5, v___x_986_);
lean_ctor_set(v___x_993_, 6, v___x_990_);
lean_ctor_set(v___x_993_, 7, v___x_992_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_993_);
v___x_995_ = v___x_965_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_999_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_995_);
v___x_997_ = v___x_961_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
lean_dec_ref(v_args_972_);
lean_del_object(v___x_965_);
lean_dec(v_val_963_);
lean_dec(v_us_956_);
lean_dec(v_declName_955_);
v___x_1000_ = lean_box(0);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_1000_);
v___x_1002_ = v___x_961_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
else
{
lean_object* v___x_1005_; 
lean_del_object(v___x_961_);
lean_dec(v_a_959_);
v___x_1005_ = lean_st_ref_get(v___y_946_);
if (v_alsoCasesOn_939_ == 0)
{
lean_dec(v___x_1005_);
lean_dec(v_us_956_);
lean_dec(v_declName_955_);
lean_dec_ref(v_e_938_);
goto v___jp_948_;
}
else
{
lean_object* v_env_1006_; uint8_t v___x_1007_; 
v_env_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc_ref(v_env_1006_);
lean_dec(v___x_1005_);
lean_inc(v_declName_955_);
v___x_1007_ = l_Lean_isCasesOnRecursor(v_env_1006_, v_declName_955_);
if (v___x_1007_ == 0)
{
lean_dec(v_us_956_);
lean_dec(v_declName_955_);
lean_dec_ref(v_e_938_);
goto v___jp_948_;
}
else
{
lean_object* v_indName_1008_; lean_object* v___x_1009_; 
v_indName_1008_ = l_Lean_Name_getPrefix(v_declName_955_);
v___x_1009_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_indName_1008_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1102_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1102_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1102_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
if (lean_obj_tag(v_a_1010_) == 5)
{
lean_object* v_val_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1097_; 
v_val_1014_ = lean_ctor_get(v_a_1010_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_a_1010_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1016_ = v_a_1010_;
v_isShared_1017_ = v_isSharedCheck_1097_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_val_1014_);
lean_dec(v_a_1010_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1097_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_toConstantVal_1018_; lean_object* v_numParams_1019_; lean_object* v_numIndices_1020_; lean_object* v_ctors_1021_; lean_object* v_nargs_1022_; lean_object* v_dummy_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_args_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_toConstantVal_1018_ = lean_ctor_get(v_val_1014_, 0);
lean_inc_ref(v_toConstantVal_1018_);
v_numParams_1019_ = lean_ctor_get(v_val_1014_, 1);
lean_inc(v_numParams_1019_);
v_numIndices_1020_ = lean_ctor_get(v_val_1014_, 2);
lean_inc(v_numIndices_1020_);
v_ctors_1021_ = lean_ctor_get(v_val_1014_, 4);
lean_inc(v_ctors_1021_);
v_nargs_1022_ = l_Lean_Expr_getAppNumArgs(v_e_938_);
v_dummy_1023_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
lean_inc(v_nargs_1022_);
v___x_1024_ = lean_mk_array(v_nargs_1022_, v_dummy_1023_);
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_nat_sub(v_nargs_1022_, v___x_1025_);
lean_dec(v_nargs_1022_);
v_args_1027_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_938_, v___x_1024_, v___x_1026_);
v___x_1028_ = lean_nat_add(v_numParams_1019_, v___x_1025_);
v___x_1029_ = lean_nat_add(v___x_1028_, v_numIndices_1020_);
v___x_1030_ = lean_nat_add(v___x_1029_, v___x_1025_);
lean_dec(v___x_1029_);
v___x_1031_ = l_Lean_InductiveVal_numCtors(v_val_1014_);
lean_dec_ref(v_val_1014_);
v___x_1032_ = lean_nat_add(v___x_1030_, v___x_1031_);
lean_dec(v___x_1031_);
v___x_1033_ = lean_array_get_size(v_args_1027_);
v___x_1034_ = lean_nat_dec_le(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
lean_dec(v___x_1032_);
lean_dec(v___x_1030_);
lean_dec(v___x_1028_);
lean_dec_ref(v_args_1027_);
lean_dec(v_ctors_1021_);
lean_dec(v_numIndices_1020_);
lean_dec(v_numParams_1019_);
lean_dec_ref(v_toConstantVal_1018_);
lean_del_object(v___x_1016_);
lean_dec(v_us_956_);
lean_dec(v_declName_955_);
v___x_1035_ = lean_box(0);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1035_);
v___x_1037_ = v___x_1012_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
else
{
lean_object* v___x_1039_; lean_object* v_params_1040_; lean_object* v_motive_1041_; lean_object* v_discrs_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v_discrInfos_1045_; lean_object* v_alts_1046_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v_lower_1088_; lean_object* v_upper_1089_; uint8_t v___x_1096_; 
lean_del_object(v___x_1012_);
v___x_1039_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1019_);
lean_inc_ref_n(v_args_1027_, 3);
v_params_1040_ = l_Array_toSubarray___redArg(v_args_1027_, v___x_1039_, v_numParams_1019_);
v_motive_1041_ = lean_array_get(v___x_957_, v_args_1027_, v_numParams_1019_);
lean_dec(v_numParams_1019_);
lean_inc(v___x_1030_);
v_discrs_1042_ = l_Array_toSubarray___redArg(v_args_1027_, v___x_1028_, v___x_1030_);
v___x_1043_ = lean_nat_add(v_numIndices_1020_, v___x_1025_);
lean_dec(v_numIndices_1020_);
v___x_1044_ = lean_box(0);
v_discrInfos_1045_ = lean_mk_array(v___x_1043_, v___x_1044_);
lean_inc(v___x_1032_);
v_alts_1046_ = l_Array_toSubarray___redArg(v_args_1027_, v___x_1030_, v___x_1032_);
v___x_1096_ = lean_nat_dec_le(v___x_1032_, v___x_1039_);
if (v___x_1096_ == 0)
{
v_lower_1088_ = v___x_1032_;
v_upper_1089_ = v___x_1033_;
goto v___jp_1087_;
}
else
{
lean_dec(v___x_1032_);
v_lower_1088_ = v___x_1039_;
v_upper_1089_ = v___x_1033_;
goto v___jp_1087_;
}
v___jp_1047_:
{
lean_object* v___x_1050_; size_t v_sz_1051_; size_t v___x_1052_; lean_object* v___x_1053_; 
v___x_1050_ = lean_array_mk(v_ctors_1021_);
v_sz_1051_ = lean_array_size(v___x_1050_);
v___x_1052_ = ((size_t)0ULL);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_1051_, v___x_1052_, v___x_1050_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1078_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1078_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1078_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_start_1058_; lean_object* v_stop_1059_; lean_object* v_start_1060_; lean_object* v_stop_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v_start_1058_ = lean_ctor_get(v_params_1040_, 1);
v_stop_1059_ = lean_ctor_get(v_params_1040_, 2);
v_start_1060_ = lean_ctor_get(v_discrs_1042_, 1);
v_stop_1061_ = lean_ctor_get(v_discrs_1042_, 2);
v___x_1062_ = lean_nat_sub(v_stop_1059_, v_start_1058_);
v___x_1063_ = lean_nat_sub(v_stop_1061_, v_start_1060_);
v___x_1064_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2);
v___x_1065_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
lean_ctor_set(v___x_1065_, 2, v_a_1054_);
lean_ctor_set(v___x_1065_, 3, v___y_1049_);
lean_ctor_set(v___x_1065_, 4, v_discrInfos_1045_);
lean_ctor_set(v___x_1065_, 5, v___x_1064_);
v___x_1066_ = lean_array_mk(v_us_956_);
v___x_1067_ = l_Subarray_copy___redArg(v_params_1040_);
v___x_1068_ = l_Subarray_copy___redArg(v_discrs_1042_);
v___x_1069_ = l_Subarray_copy___redArg(v_alts_1046_);
v___x_1070_ = l_Subarray_copy___redArg(v___y_1048_);
v___x_1071_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1065_);
lean_ctor_set(v___x_1071_, 1, v_declName_955_);
lean_ctor_set(v___x_1071_, 2, v___x_1066_);
lean_ctor_set(v___x_1071_, 3, v___x_1067_);
lean_ctor_set(v___x_1071_, 4, v_motive_1041_);
lean_ctor_set(v___x_1071_, 5, v___x_1068_);
lean_ctor_set(v___x_1071_, 6, v___x_1069_);
lean_ctor_set(v___x_1071_, 7, v___x_1070_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set_tag(v___x_1016_, 1);
lean_ctor_set(v___x_1016_, 0, v___x_1071_);
v___x_1073_ = v___x_1016_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1075_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v___x_1073_);
v___x_1075_ = v___x_1056_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1073_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec_ref(v_alts_1046_);
lean_dec_ref(v_discrInfos_1045_);
lean_dec_ref(v_discrs_1042_);
lean_dec(v_motive_1041_);
lean_dec_ref(v_params_1040_);
lean_del_object(v___x_1016_);
lean_dec(v_us_956_);
lean_dec(v_declName_955_);
v_a_1079_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1053_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1053_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
v___jp_1087_:
{
lean_object* v_levelParams_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v_levelParams_1090_ = lean_ctor_get(v_toConstantVal_1018_, 1);
lean_inc(v_levelParams_1090_);
lean_dec_ref(v_toConstantVal_1018_);
v___x_1091_ = l_Array_toSubarray___redArg(v_args_1027_, v_lower_1088_, v_upper_1089_);
v___x_1092_ = l_List_lengthTR___redArg(v_levelParams_1090_);
lean_dec(v_levelParams_1090_);
v___x_1093_ = l_List_lengthTR___redArg(v_us_956_);
v___x_1094_ = lean_nat_dec_eq(v___x_1092_, v___x_1093_);
lean_dec(v___x_1093_);
lean_dec(v___x_1092_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; 
v___x_1095_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3));
v___y_1048_ = v___x_1091_;
v___y_1049_ = v___x_1095_;
goto v___jp_1047_;
}
else
{
v___y_1048_ = v___x_1091_;
v___y_1049_ = v___x_1044_;
goto v___jp_1047_;
}
}
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v___x_1100_; 
lean_dec(v_a_1010_);
lean_dec(v_us_956_);
lean_dec(v_declName_955_);
lean_dec_ref(v_e_938_);
v___x_1098_ = lean_box(0);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1098_);
v___x_1100_ = v___x_1012_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_us_956_);
lean_dec(v_declName_955_);
lean_dec_ref(v_e_938_);
v_a_1103_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1009_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1009_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
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
lean_dec_ref(v___x_954_);
lean_dec_ref(v_e_938_);
goto v___jp_948_;
}
}
v___jp_948_:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_box(0);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object* v_e_1112_, lean_object* v_alsoCasesOn_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1122_; lean_object* v_res_1123_; 
v_alsoCasesOn_boxed_1122_ = lean_unbox(v_alsoCasesOn_1113_);
v_res_1123_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1112_, v_alsoCasesOn_boxed_1122_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
lean_dec(v___y_1114_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_bs_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_usize_dec_lt(v_i_1125_, v_sz_1124_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_bs_1126_);
return v___x_1133_;
}
else
{
lean_object* v_v_1134_; lean_object* v___x_1135_; lean_object* v_bs_x27_1136_; lean_object* v___x_1137_; 
v_v_1134_ = lean_array_uget(v_bs_1126_, v_i_1125_);
v___x_1135_ = lean_unsigned_to_nat(0u);
v_bs_x27_1136_ = lean_array_uset(v_bs_1126_, v_i_1125_, v___x_1135_);
v___x_1137_ = l_Lean_Elab_WF_mkWfParam(v_v_1134_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; size_t v___x_1139_; size_t v___x_1140_; lean_object* v___x_1141_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = ((size_t)1ULL);
v___x_1140_ = lean_usize_add(v_i_1125_, v___x_1139_);
v___x_1141_ = lean_array_uset(v_bs_x27_1136_, v_i_1125_, v_a_1138_);
v_i_1125_ = v___x_1140_;
v_bs_1126_ = v___x_1141_;
goto _start;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_dec_ref(v_bs_x27_1136_);
v_a_1143_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1137_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1137_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_bs_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
size_t v_sz_boxed_1159_; size_t v_i_boxed_1160_; lean_object* v_res_1161_; 
v_sz_boxed_1159_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1160_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_boxed_1159_, v_i_boxed_1160_, v_bs_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(uint8_t v___x_1162_, lean_object* v_xs_1163_, lean_object* v_body_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
v_sz_1173_ = lean_array_size(v_xs_1163_);
v___x_1174_ = ((size_t)0ULL);
lean_inc_ref(v_xs_1163_);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1173_, v___x_1174_, v_xs_1163_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = l_Lean_Expr_replaceFVars(v_body_1164_, v_xs_1163_, v_a_1176_);
lean_dec(v_a_1176_);
v___x_1178_ = 0;
v___x_1179_ = 1;
v___x_1180_ = l_Lean_Meta_mkLambdaFVars(v_xs_1163_, v___x_1177_, v___x_1178_, v___x_1162_, v___x_1178_, v___x_1162_, v___x_1179_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec_ref(v_xs_1163_);
return v___x_1180_;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v_xs_1163_);
v_a_1181_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1175_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1175_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0___boxed(lean_object* v___x_1189_, lean_object* v_xs_1190_, lean_object* v_body_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v___x_22056__boxed_1200_; lean_object* v_res_1201_; 
v___x_22056__boxed_1200_ = lean_unbox(v___x_1189_);
v_res_1201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0(v___x_22056__boxed_1200_, v_xs_1190_, v_body_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v_body_1191_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t v_sz_1202_, size_t v_i_1203_, lean_object* v_bs_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
uint8_t v___x_1213_; 
v___x_1213_ = lean_usize_dec_lt(v_i_1203_, v_sz_1202_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_bs_1204_);
return v___x_1214_;
}
else
{
lean_object* v___x_1215_; lean_object* v___f_1216_; lean_object* v_v_1217_; lean_object* v___x_1218_; lean_object* v_bs_x27_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; 
v___x_1215_ = lean_box(v___x_1213_);
v___f_1216_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___lam__0___boxed), 11, 1);
lean_closure_set(v___f_1216_, 0, v___x_1215_);
v_v_1217_ = lean_array_uget(v_bs_1204_, v_i_1203_);
v___x_1218_ = lean_unsigned_to_nat(0u);
v_bs_x27_1219_ = lean_array_uset(v_bs_1204_, v_i_1203_, v___x_1218_);
v___x_1220_ = 0;
v___x_1221_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_v_1217_, v___f_1216_, v___x_1220_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; size_t v___x_1223_; size_t v___x_1224_; lean_object* v___x_1225_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = ((size_t)1ULL);
v___x_1224_ = lean_usize_add(v_i_1203_, v___x_1223_);
v___x_1225_ = lean_array_uset(v_bs_x27_1219_, v_i_1203_, v_a_1222_);
v_i_1203_ = v___x_1224_;
v_bs_1204_ = v___x_1225_;
goto _start;
}
else
{
lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1234_; 
lean_dec_ref(v_bs_x27_1219_);
v_a_1227_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1229_ = v___x_1221_;
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_dec(v___x_1221_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1234_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1230_ == 0)
{
v___x_1232_ = v___x_1229_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1227_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object* v_sz_1235_, lean_object* v_i_1236_, lean_object* v_bs_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
size_t v_sz_boxed_1246_; size_t v_i_boxed_1247_; lean_object* v_res_1248_; 
v_sz_boxed_1246_ = lean_unbox_usize(v_sz_1235_);
lean_dec(v_sz_1235_);
v_i_boxed_1247_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_boxed_1246_, v_i_boxed_1247_, v_bs_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
return v_res_1248_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object* v_as_1249_, size_t v_i_1250_, size_t v_stop_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_eq(v_i_1250_, v_stop_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_array_uget_borrowed(v_as_1249_, v_i_1250_);
v___x_1254_ = l_Lean_Elab_WF_isWfParam_x3f(v___x_1253_);
if (lean_obj_tag(v___x_1254_) == 0)
{
size_t v___x_1255_; size_t v___x_1256_; 
v___x_1255_ = ((size_t)1ULL);
v___x_1256_ = lean_usize_add(v_i_1250_, v___x_1255_);
v_i_1250_ = v___x_1256_;
goto _start;
}
else
{
uint8_t v___x_1258_; 
lean_dec_ref_known(v___x_1254_, 1);
v___x_1258_ = 1;
return v___x_1258_;
}
}
else
{
uint8_t v___x_1259_; 
v___x_1259_ = 0;
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object* v_as_1260_, lean_object* v_i_1261_, lean_object* v_stop_1262_){
_start:
{
size_t v_i_boxed_1263_; size_t v_stop_boxed_1264_; uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_i_boxed_1263_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_stop_boxed_1264_ = lean_unbox_usize(v_stop_1262_);
lean_dec(v_stop_1262_);
v_res_1265_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1260_, v_i_boxed_1263_, v_stop_boxed_1264_);
lean_dec_ref(v_as_1260_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher(lean_object* v_e_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
uint8_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = 1;
v___x_1277_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1267_, v___x_1276_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1277_) == 0)
{
lean_object* v_a_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1340_; 
v_a_1278_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1280_ = v___x_1277_;
v_isShared_1281_ = v_isSharedCheck_1340_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_a_1278_);
lean_dec(v___x_1277_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1340_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
if (lean_obj_tag(v_a_1278_) == 1)
{
lean_object* v_val_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1337_; 
v_val_1287_ = lean_ctor_get(v_a_1278_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_a_1278_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1289_ = v_a_1278_;
v_isShared_1290_ = v_isSharedCheck_1337_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_val_1287_);
lean_dec(v_a_1278_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1337_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v_toMatcherInfo_1291_; lean_object* v_matcherName_1292_; lean_object* v_matcherLevels_1293_; lean_object* v_params_1294_; lean_object* v_motive_1295_; lean_object* v_discrs_1296_; lean_object* v_alts_1297_; lean_object* v_remaining_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1336_; 
v_toMatcherInfo_1291_ = lean_ctor_get(v_val_1287_, 0);
v_matcherName_1292_ = lean_ctor_get(v_val_1287_, 1);
v_matcherLevels_1293_ = lean_ctor_get(v_val_1287_, 2);
v_params_1294_ = lean_ctor_get(v_val_1287_, 3);
v_motive_1295_ = lean_ctor_get(v_val_1287_, 4);
v_discrs_1296_ = lean_ctor_get(v_val_1287_, 5);
v_alts_1297_ = lean_ctor_get(v_val_1287_, 6);
v_remaining_1298_ = lean_ctor_get(v_val_1287_, 7);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_val_1287_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1300_ = v_val_1287_;
v_isShared_1301_ = v_isSharedCheck_1336_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_remaining_1298_);
lean_inc(v_alts_1297_);
lean_inc(v_discrs_1296_);
lean_inc(v_motive_1295_);
lean_inc(v_params_1294_);
lean_inc(v_matcherLevels_1293_);
lean_inc(v_matcherName_1292_);
lean_inc(v_toMatcherInfo_1291_);
lean_dec(v_val_1287_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1336_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1302_ = lean_unsigned_to_nat(0u);
v___x_1303_ = lean_array_get_size(v_discrs_1296_);
v___x_1304_ = lean_nat_dec_lt(v___x_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_del_object(v___x_1300_);
lean_dec_ref(v_remaining_1298_);
lean_dec_ref(v_alts_1297_);
lean_dec_ref(v_discrs_1296_);
lean_dec_ref(v_motive_1295_);
lean_dec_ref(v_params_1294_);
lean_dec_ref(v_matcherLevels_1293_);
lean_dec(v_matcherName_1292_);
lean_dec_ref(v_toMatcherInfo_1291_);
lean_del_object(v___x_1289_);
goto v___jp_1282_;
}
else
{
if (v___x_1304_ == 0)
{
lean_del_object(v___x_1300_);
lean_dec_ref(v_remaining_1298_);
lean_dec_ref(v_alts_1297_);
lean_dec_ref(v_discrs_1296_);
lean_dec_ref(v_motive_1295_);
lean_dec_ref(v_params_1294_);
lean_dec_ref(v_matcherLevels_1293_);
lean_dec(v_matcherName_1292_);
lean_dec_ref(v_toMatcherInfo_1291_);
lean_del_object(v___x_1289_);
goto v___jp_1282_;
}
else
{
size_t v___x_1305_; size_t v___x_1306_; uint8_t v___x_1307_; 
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = lean_usize_of_nat(v___x_1303_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_discrs_1296_, v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_del_object(v___x_1300_);
lean_dec_ref(v_remaining_1298_);
lean_dec_ref(v_alts_1297_);
lean_dec_ref(v_discrs_1296_);
lean_dec_ref(v_motive_1295_);
lean_dec_ref(v_params_1294_);
lean_dec_ref(v_matcherLevels_1293_);
lean_dec(v_matcherName_1292_);
lean_dec_ref(v_toMatcherInfo_1291_);
lean_del_object(v___x_1289_);
goto v___jp_1282_;
}
else
{
size_t v_sz_1308_; lean_object* v___x_1309_; size_t v_sz_1310_; lean_object* v___x_1311_; 
lean_del_object(v___x_1280_);
v_sz_1308_ = lean_array_size(v_discrs_1296_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_1308_, v___x_1305_, v_discrs_1296_);
v_sz_1310_ = lean_array_size(v_alts_1297_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1310_, v___x_1305_, v_alts_1297_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1327_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1327_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 6, v_a_1312_);
lean_ctor_set(v___x_1300_, 5, v___x_1309_);
v___x_1317_ = v___x_1300_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_toMatcherInfo_1291_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_matcherName_1292_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_matcherLevels_1293_);
lean_ctor_set(v_reuseFailAlloc_1326_, 3, v_params_1294_);
lean_ctor_set(v_reuseFailAlloc_1326_, 4, v_motive_1295_);
lean_ctor_set(v_reuseFailAlloc_1326_, 5, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1326_, 6, v_a_1312_);
lean_ctor_set(v_reuseFailAlloc_1326_, 7, v_remaining_1298_);
v___x_1317_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = l_Lean_Meta_MatcherApp_toExpr(v___x_1317_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1318_);
v___x_1320_ = v___x_1289_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1321_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1321_);
v___x_1323_ = v___x_1314_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
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
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v___x_1309_);
lean_del_object(v___x_1300_);
lean_dec_ref(v_remaining_1298_);
lean_dec_ref(v_motive_1295_);
lean_dec_ref(v_params_1294_);
lean_dec_ref(v_matcherLevels_1293_);
lean_dec(v_matcherName_1292_);
lean_dec_ref(v_toMatcherInfo_1291_);
lean_del_object(v___x_1289_);
v_a_1328_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1311_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1311_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
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
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_del_object(v___x_1280_);
lean_dec(v_a_1278_);
v___x_1338_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
return v___x_1339_;
}
v___jp_1282_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
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
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_a_1341_ = lean_ctor_get(v___x_1277_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1277_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1277_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1277_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Elab_WF_paramMatcher(v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t v_sz_1359_, size_t v_i_1360_, lean_object* v_bs_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1359_, v_i_1360_, v_bs_1361_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object* v_sz_1371_, lean_object* v_i_1372_, lean_object* v_bs_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
size_t v_sz_boxed_1382_; size_t v_i_boxed_1383_; lean_object* v_res_1384_; 
v_sz_boxed_1382_ = lean_unbox_usize(v_sz_1371_);
lean_dec(v_sz_1371_);
v_i_boxed_1383_ = lean_unbox_usize(v_i_1372_);
lean_dec(v_i_1372_);
v_res_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_boxed_1382_, v_i_boxed_1383_, v_bs_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object* v_declName_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1385_, v___y_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object* v_declName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
lean_dec(v___y_1396_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_1405_, lean_object* v_constName_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_constName_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(v_00_u03b1_1416_, v_constName_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b1_1427_, lean_object* v_ref_1428_, lean_object* v_constName_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_1428_, v_constName_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b1_1439_, lean_object* v_ref_1440_, lean_object* v_constName_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(v_00_u03b1_1439_, v_ref_1440_, v_constName_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
lean_dec(v_ref_1440_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_1451_, lean_object* v_ref_1452_, lean_object* v_msg_1453_, lean_object* v_declHint_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_1452_, v_msg_1453_, v_declHint_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1464_, lean_object* v_ref_1465_, lean_object* v_msg_1466_, lean_object* v_declHint_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_1464_, v_ref_1465_, v_msg_1466_, v_declHint_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec(v_ref_1465_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1477_, lean_object* v_declHint_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1477_, v_declHint_1478_, v___y_1485_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1488_, lean_object* v_declHint_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1488_, v_declHint_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1499_, lean_object* v_ref_1500_, lean_object* v_msg_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_1500_, v_msg_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_ref_1512_, lean_object* v_msg_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(v_00_u03b1_1511_, v_ref_1512_, v_msg_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v_ref_1512_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_1523_, lean_object* v_msg_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_1524_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1534_, lean_object* v_msg_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(v_00_u03b1_1534_, v_msg_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
lean_dec(v___y_1536_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1552_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_));
v___x_1553_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_1554_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1555_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1552_, v___x_1553_, v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10____boxed(lean_object* v_a_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_();
return v_res_1557_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object* v_e_1558_){
_start:
{
if (lean_obj_tag(v_e_1558_) == 8)
{
lean_object* v_value_1559_; lean_object* v_body_1560_; lean_object* v___x_1561_; 
v_value_1559_ = lean_ctor_get(v_e_1558_, 2);
v_body_1560_ = lean_ctor_get(v_e_1558_, 3);
v___x_1561_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1559_);
if (lean_obj_tag(v___x_1561_) == 0)
{
v_e_1558_ = v_body_1560_;
goto _start;
}
else
{
uint8_t v___x_1563_; 
lean_dec_ref_known(v___x_1561_, 1);
v___x_1563_ = 1;
return v___x_1563_;
}
}
else
{
uint8_t v___x_1564_; 
v___x_1564_ = 0;
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object* v_e_1565_){
_start:
{
uint8_t v_res_1566_; lean_object* v_r_1567_; 
v_res_1566_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1565_);
lean_dec_ref(v_e_1565_);
v_r_1567_ = lean_box(v_res_1566_);
return v_r_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object* v_e_1568_, lean_object* v_acc_1569_){
_start:
{
if (lean_obj_tag(v_e_1568_) == 8)
{
lean_object* v_value_1570_; lean_object* v_body_1571_; lean_object* v___x_1572_; 
v_value_1570_ = lean_ctor_get(v_e_1568_, 2);
v_body_1571_ = lean_ctor_get(v_e_1568_, 3);
v___x_1572_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1570_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_unsigned_to_nat(1u);
v___x_1574_ = lean_nat_add(v_acc_1569_, v___x_1573_);
lean_dec(v_acc_1569_);
v_e_1568_ = v_body_1571_;
v_acc_1569_ = v___x_1574_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_1572_, 1);
return v_acc_1569_;
}
}
else
{
return v_acc_1569_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object* v_e_1576_, lean_object* v_acc_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1576_, v_acc_1577_);
lean_dec_ref(v_e_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object* v_msg_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v___f_1586_; lean_object* v___x_1085__overap_1587_; lean_object* v___x_1588_; 
v___f_1586_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0));
v___x_1085__overap_1587_ = lean_panic_fn_borrowed(v___f_1586_, v_msg_1580_);
lean_inc(v___y_1584_);
lean_inc_ref(v___y_1583_);
lean_inc(v___y_1582_);
lean_inc_ref(v___y_1581_);
v___x_1588_ = lean_apply_5(v___x_1085__overap_1587_, v___y_1581_, v___y_1582_, v___y_1583_, v___y_1584_, lean_box(0));
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object* v_msg_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object* v_k_1596_, lean_object* v_b_1597_, lean_object* v_c_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v___x_1604_; 
lean_inc(v___y_1602_);
lean_inc_ref(v___y_1601_);
lean_inc(v___y_1600_);
lean_inc_ref(v___y_1599_);
v___x_1604_ = lean_apply_7(v_k_1596_, v_b_1597_, v_c_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, lean_box(0));
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object* v_k_1605_, lean_object* v_b_1606_, lean_object* v_c_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1605_, v_b_1606_, v_c_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object* v_e_1614_, lean_object* v_maxFVars_x3f_1615_, lean_object* v_k_1616_, uint8_t v_cleanupAnnotations_1617_, uint8_t v_preserveNondepLet_1618_, uint8_t v_nondepLetOnly_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___f_1625_; uint8_t v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; 
v___f_1625_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1625_, 0, v_k_1616_);
v___x_1626_ = 0;
v___x_1627_ = 1;
v___x_1628_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1614_, v___x_1626_, v___x_1627_, v_preserveNondepLet_1618_, v_nondepLetOnly_1619_, v_maxFVars_x3f_1615_, v___f_1625_, v_cleanupAnnotations_1617_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1644_; 
v_a_1637_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1639_ = v___x_1628_;
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1628_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1644_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1642_; 
if (v_isShared_1640_ == 0)
{
v___x_1642_ = v___x_1639_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1637_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object* v_e_1645_, lean_object* v_maxFVars_x3f_1646_, lean_object* v_k_1647_, lean_object* v_cleanupAnnotations_1648_, lean_object* v_preserveNondepLet_1649_, lean_object* v_nondepLetOnly_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1656_; uint8_t v_preserveNondepLet_boxed_1657_; uint8_t v_nondepLetOnly_boxed_1658_; lean_object* v_res_1659_; 
v_cleanupAnnotations_boxed_1656_ = lean_unbox(v_cleanupAnnotations_1648_);
v_preserveNondepLet_boxed_1657_ = lean_unbox(v_preserveNondepLet_1649_);
v_nondepLetOnly_boxed_1658_ = lean_unbox(v_nondepLetOnly_1650_);
v_res_1659_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1645_, v_maxFVars_x3f_1646_, v_k_1647_, v_cleanupAnnotations_boxed_1656_, v_preserveNondepLet_boxed_1657_, v_nondepLetOnly_boxed_1658_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v_maxFVars_x3f_1646_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object* v_00_u03b1_1660_, lean_object* v_e_1661_, lean_object* v_maxFVars_x3f_1662_, lean_object* v_k_1663_, uint8_t v_cleanupAnnotations_1664_, uint8_t v_preserveNondepLet_1665_, uint8_t v_nondepLetOnly_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1661_, v_maxFVars_x3f_1662_, v_k_1663_, v_cleanupAnnotations_1664_, v_preserveNondepLet_1665_, v_nondepLetOnly_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object* v_00_u03b1_1673_, lean_object* v_e_1674_, lean_object* v_maxFVars_x3f_1675_, lean_object* v_k_1676_, lean_object* v_cleanupAnnotations_1677_, lean_object* v_preserveNondepLet_1678_, lean_object* v_nondepLetOnly_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1685_; uint8_t v_preserveNondepLet_boxed_1686_; uint8_t v_nondepLetOnly_boxed_1687_; lean_object* v_res_1688_; 
v_cleanupAnnotations_boxed_1685_ = lean_unbox(v_cleanupAnnotations_1677_);
v_preserveNondepLet_boxed_1686_ = lean_unbox(v_preserveNondepLet_1678_);
v_nondepLetOnly_boxed_1687_ = lean_unbox(v_nondepLetOnly_1679_);
v_res_1688_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(v_00_u03b1_1673_, v_e_1674_, v_maxFVars_x3f_1675_, v_k_1676_, v_cleanupAnnotations_boxed_1685_, v_preserveNondepLet_boxed_1686_, v_nondepLetOnly_boxed_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_maxFVars_x3f_1675_);
return v_res_1688_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_unsigned_to_nat(0u);
v___x_1690_ = l_Lean_Expr_bvar___override(v___x_1689_);
return v___x_1690_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1694_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3));
v___x_1695_ = lean_unsigned_to_nat(6u);
v___x_1696_ = lean_unsigned_to_nat(142u);
v___x_1697_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2));
v___x_1698_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1));
v___x_1699_ = l_mkPanicMessageWithDecl(v___x_1698_, v___x_1697_, v___x_1696_, v___x_1695_, v___x_1694_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object* v_xs_1700_, lean_object* v_b_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1700_, v_b_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec_ref(v_xs_1700_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object* v_e_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_){
_start:
{
if (lean_obj_tag(v_e_1708_) == 8)
{
lean_object* v_declName_1714_; lean_object* v_type_1715_; lean_object* v_value_1716_; lean_object* v_body_1717_; uint8_t v_nondep_1718_; lean_object* v___x_1719_; 
v_declName_1714_ = lean_ctor_get(v_e_1708_, 0);
v_type_1715_ = lean_ctor_get(v_e_1708_, 1);
v_value_1716_ = lean_ctor_get(v_e_1708_, 2);
v_body_1717_ = lean_ctor_get(v_e_1708_, 3);
v_nondep_1718_ = lean_ctor_get_uint8(v_e_1708_, sizeof(void*)*4 + 8);
v___x_1719_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1716_);
if (lean_obj_tag(v___x_1719_) == 1)
{
lean_object* v_val_1720_; lean_object* v___x_1721_; 
v_val_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_val_1720_);
lean_dec_ref_known(v___x_1719_, 1);
lean_inc_ref(v_type_1715_);
v___x_1721_ = l_Lean_Meta_isProp(v_type_1715_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; uint8_t v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = lean_unbox(v_a_1722_);
lean_dec(v_a_1722_);
if (v___x_1723_ == 0)
{
lean_object* v___x_1724_; 
lean_inc_ref(v_type_1715_);
v___x_1724_ = l_Lean_Meta_getLevel(v_type_1715_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; size_t v___x_1733_; uint8_t v___x_1734_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_1727_ = lean_box(0);
v___x_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_a_1725_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_Expr_const___override(v___x_1726_, v___x_1728_);
v___x_1730_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0);
lean_inc_ref(v_type_1715_);
v___x_1731_ = l_Lean_mkAppB(v___x_1729_, v_type_1715_, v___x_1730_);
v___x_1732_ = lean_expr_instantiate1(v_body_1717_, v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1733_ = lean_ptr_addr(v_type_1715_);
v___x_1734_ = lean_usize_dec_eq(v___x_1733_, v___x_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
lean_inc_ref(v_type_1715_);
lean_inc(v_declName_1714_);
lean_dec_ref_known(v_e_1708_, 4);
v___x_1735_ = l_Lean_Expr_letE___override(v_declName_1714_, v_type_1715_, v_val_1720_, v___x_1732_, v_nondep_1718_);
v_e_1708_ = v___x_1735_;
goto _start;
}
else
{
size_t v___x_1737_; size_t v___x_1738_; uint8_t v___x_1739_; 
v___x_1737_ = lean_ptr_addr(v_value_1716_);
v___x_1738_ = lean_ptr_addr(v_val_1720_);
v___x_1739_ = lean_usize_dec_eq(v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
lean_inc_ref(v_type_1715_);
lean_inc(v_declName_1714_);
lean_dec_ref_known(v_e_1708_, 4);
v___x_1740_ = l_Lean_Expr_letE___override(v_declName_1714_, v_type_1715_, v_val_1720_, v___x_1732_, v_nondep_1718_);
v_e_1708_ = v___x_1740_;
goto _start;
}
else
{
size_t v___x_1742_; size_t v___x_1743_; uint8_t v___x_1744_; 
v___x_1742_ = lean_ptr_addr(v_body_1717_);
v___x_1743_ = lean_ptr_addr(v___x_1732_);
v___x_1744_ = lean_usize_dec_eq(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; 
lean_inc_ref(v_type_1715_);
lean_inc(v_declName_1714_);
lean_dec_ref_known(v_e_1708_, 4);
v___x_1745_ = l_Lean_Expr_letE___override(v_declName_1714_, v_type_1715_, v_val_1720_, v___x_1732_, v_nondep_1718_);
v_e_1708_ = v___x_1745_;
goto _start;
}
else
{
lean_dec_ref(v___x_1732_);
lean_dec(v_val_1720_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_val_1720_);
lean_dec_ref_known(v_e_1708_, 4);
v_a_1748_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1724_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1724_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
size_t v___x_1756_; uint8_t v___x_1757_; 
v___x_1756_ = lean_ptr_addr(v_type_1715_);
v___x_1757_ = lean_usize_dec_eq(v___x_1756_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; 
lean_inc_ref(v_body_1717_);
lean_inc_ref(v_type_1715_);
lean_inc(v_declName_1714_);
lean_dec_ref_known(v_e_1708_, 4);
v___x_1758_ = l_Lean_Expr_letE___override(v_declName_1714_, v_type_1715_, v_val_1720_, v_body_1717_, v_nondep_1718_);
v_e_1708_ = v___x_1758_;
goto _start;
}
else
{
size_t v___x_1760_; size_t v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = lean_ptr_addr(v_value_1716_);
v___x_1761_ = lean_ptr_addr(v_val_1720_);
v___x_1762_ = lean_usize_dec_eq(v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; 
lean_inc_ref(v_body_1717_);
lean_inc_ref(v_type_1715_);
lean_inc(v_declName_1714_);
lean_dec_ref_known(v_e_1708_, 4);
v___x_1763_ = l_Lean_Expr_letE___override(v_declName_1714_, v_type_1715_, v_val_1720_, v_body_1717_, v_nondep_1718_);
v_e_1708_ = v___x_1763_;
goto _start;
}
else
{
size_t v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_ptr_addr(v_body_1717_);
v___x_1766_ = lean_usize_dec_eq(v___x_1765_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_inc_ref(v_body_1717_);
lean_inc_ref(v_type_1715_);
lean_inc(v_declName_1714_);
lean_dec_ref_known(v_e_1708_, 4);
v___x_1767_ = l_Lean_Expr_letE___override(v_declName_1714_, v_type_1715_, v_val_1720_, v_body_1717_, v_nondep_1718_);
v_e_1708_ = v___x_1767_;
goto _start;
}
else
{
lean_dec(v_val_1720_);
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_val_1720_);
lean_dec_ref_known(v_e_1708_, 4);
v_a_1770_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1721_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1721_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v___x_1778_; lean_object* v_num_1779_; uint8_t v___x_1780_; 
lean_dec(v___x_1719_);
v___x_1778_ = lean_unsigned_to_nat(0u);
v_num_1779_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1708_, v___x_1778_);
v___x_1780_ = lean_nat_dec_lt(v___x_1778_, v_num_1779_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v_num_1779_);
lean_dec_ref_known(v_e_1708_, 4);
v___x_1781_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4);
v___x_1782_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v___x_1781_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
return v___x_1782_;
}
else
{
lean_object* v___f_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; 
v___f_1783_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed), 7, 0);
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v_num_1779_);
v___x_1785_ = 0;
v___x_1786_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1708_, v___x_1784_, v___f_1783_, v___x_1785_, v___x_1780_, v___x_1785_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_);
lean_dec_ref_known(v___x_1784_, 1);
return v___x_1786_;
}
}
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v_e_1708_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object* v_xs_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_b_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_object* v_a_1796_; uint8_t v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; 
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v___x_1797_ = 0;
v___x_1798_ = 1;
v___x_1799_ = l_Lean_Meta_mkLetFVars(v_xs_1788_, v_a_1796_, v___x_1797_, v___x_1797_, v___x_1798_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v___x_1799_;
}
else
{
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object* v_e_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object* v_e_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Lean_Expr_isLet(v_e_1807_);
if (v___x_1833_ == 0)
{
uint8_t v___x_1834_; 
v___x_1834_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1807_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v_e_1807_);
v___x_1835_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
else
{
goto v___jp_1813_;
}
}
else
{
goto v___jp_1813_;
}
v___jp_1813_:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1824_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1824_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1815_);
v___x_1820_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1820_);
v___x_1822_ = v___x_1817_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_a_1825_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1814_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1814_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object* v_e_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet(lean_object* v_e_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1844_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object* v_e_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_Elab_WF_paramLet(v_e_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_a_1861_);
lean_dec_ref(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_));
v___x_1872_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_1873_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1874_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1871_, v___x_1872_, v___x_1873_);
return v___x_1874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10____boxed(lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_();
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object* v_lctx_1877_, lean_object* v_x_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_keyedConfig_1884_; uint8_t v_trackZetaDelta_1885_; lean_object* v_zetaDeltaSet_1886_; lean_object* v_localInstances_1887_; lean_object* v_defEqCtx_x3f_1888_; lean_object* v_synthPendingDepth_1889_; lean_object* v_customCanUnfoldPredicate_x3f_1890_; uint8_t v_univApprox_1891_; uint8_t v_inTypeClassResolution_1892_; uint8_t v_cacheInferType_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v_keyedConfig_1884_ = lean_ctor_get(v___y_1879_, 0);
v_trackZetaDelta_1885_ = lean_ctor_get_uint8(v___y_1879_, sizeof(void*)*7);
v_zetaDeltaSet_1886_ = lean_ctor_get(v___y_1879_, 1);
v_localInstances_1887_ = lean_ctor_get(v___y_1879_, 3);
v_defEqCtx_x3f_1888_ = lean_ctor_get(v___y_1879_, 4);
v_synthPendingDepth_1889_ = lean_ctor_get(v___y_1879_, 5);
v_customCanUnfoldPredicate_x3f_1890_ = lean_ctor_get(v___y_1879_, 6);
v_univApprox_1891_ = lean_ctor_get_uint8(v___y_1879_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1892_ = lean_ctor_get_uint8(v___y_1879_, sizeof(void*)*7 + 2);
v_cacheInferType_1893_ = lean_ctor_get_uint8(v___y_1879_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1890_);
lean_inc(v_synthPendingDepth_1889_);
lean_inc(v_defEqCtx_x3f_1888_);
lean_inc_ref(v_localInstances_1887_);
lean_inc(v_zetaDeltaSet_1886_);
lean_inc_ref(v_keyedConfig_1884_);
v___x_1894_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1894_, 0, v_keyedConfig_1884_);
lean_ctor_set(v___x_1894_, 1, v_zetaDeltaSet_1886_);
lean_ctor_set(v___x_1894_, 2, v_lctx_1877_);
lean_ctor_set(v___x_1894_, 3, v_localInstances_1887_);
lean_ctor_set(v___x_1894_, 4, v_defEqCtx_x3f_1888_);
lean_ctor_set(v___x_1894_, 5, v_synthPendingDepth_1889_);
lean_ctor_set(v___x_1894_, 6, v_customCanUnfoldPredicate_x3f_1890_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*7, v_trackZetaDelta_1885_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*7 + 1, v_univApprox_1891_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1892_);
lean_ctor_set_uint8(v___x_1894_, sizeof(void*)*7 + 3, v_cacheInferType_1893_);
lean_inc(v___y_1882_);
lean_inc_ref(v___y_1881_);
lean_inc(v___y_1880_);
v___x_1895_ = lean_apply_5(v_x_1878_, v___x_1894_, v___y_1880_, v___y_1881_, v___y_1882_, lean_box(0));
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object* v_lctx_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1896_, v_x_1897_, v___y_1898_, v___y_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
return v_res_1903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object* v_00_u03b1_1904_, lean_object* v_lctx_1905_, lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1905_, v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object* v_00_u03b1_1913_, lean_object* v_lctx_1914_, lean_object* v_x_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(v_00_u03b1_1913_, v_lctx_1914_, v_x_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object* v_e_1922_, lean_object* v_k_1923_, uint8_t v_cleanupAnnotations_1924_, uint8_t v_preserveNondepLet_1925_, uint8_t v_nondepLetOnly_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___f_1932_; uint8_t v___x_1933_; uint8_t v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1932_, 0, v_k_1923_);
v___x_1933_ = 0;
v___x_1934_ = 1;
v___x_1935_ = lean_box(0);
v___x_1936_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1922_, v___x_1933_, v___x_1934_, v_preserveNondepLet_1925_, v_nondepLetOnly_1926_, v___x_1935_, v___f_1932_, v_cleanupAnnotations_1924_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
v_a_1945_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1936_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1936_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object* v_e_1953_, lean_object* v_k_1954_, lean_object* v_cleanupAnnotations_1955_, lean_object* v_preserveNondepLet_1956_, lean_object* v_nondepLetOnly_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1963_; uint8_t v_preserveNondepLet_boxed_1964_; uint8_t v_nondepLetOnly_boxed_1965_; lean_object* v_res_1966_; 
v_cleanupAnnotations_boxed_1963_ = lean_unbox(v_cleanupAnnotations_1955_);
v_preserveNondepLet_boxed_1964_ = lean_unbox(v_preserveNondepLet_1956_);
v_nondepLetOnly_boxed_1965_ = lean_unbox(v_nondepLetOnly_1957_);
v_res_1966_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_1953_, v_k_1954_, v_cleanupAnnotations_boxed_1963_, v_preserveNondepLet_boxed_1964_, v_nondepLetOnly_boxed_1965_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object* v_00_u03b1_1967_, lean_object* v_e_1968_, lean_object* v_k_1969_, uint8_t v_cleanupAnnotations_1970_, uint8_t v_preserveNondepLet_1971_, uint8_t v_nondepLetOnly_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_1968_, v_k_1969_, v_cleanupAnnotations_1970_, v_preserveNondepLet_1971_, v_nondepLetOnly_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object* v_00_u03b1_1979_, lean_object* v_e_1980_, lean_object* v_k_1981_, lean_object* v_cleanupAnnotations_1982_, lean_object* v_preserveNondepLet_1983_, lean_object* v_nondepLetOnly_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1990_; uint8_t v_preserveNondepLet_boxed_1991_; uint8_t v_nondepLetOnly_boxed_1992_; lean_object* v_res_1993_; 
v_cleanupAnnotations_boxed_1990_ = lean_unbox(v_cleanupAnnotations_1982_);
v_preserveNondepLet_boxed_1991_ = lean_unbox(v_preserveNondepLet_1983_);
v_nondepLetOnly_boxed_1992_ = lean_unbox(v_nondepLetOnly_1984_);
v_res_1993_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(v_00_u03b1_1979_, v_e_1980_, v_k_1981_, v_cleanupAnnotations_boxed_1990_, v_preserveNondepLet_boxed_1991_, v_nondepLetOnly_boxed_1992_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object* v_e_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_e_1994_);
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object* v_e_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object* v_as_2009_, size_t v_i_2010_, size_t v_stop_2011_, lean_object* v_b_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_eq(v_i_2010_, v_stop_2011_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_array_uget_borrowed(v_as_2009_, v_i_2010_);
v___x_2020_ = l_Lean_Expr_fvarId_x21(v___x_2019_);
v___x_2021_ = l_Lean_FVarId_getDecl___redArg(v___x_2020_, v___y_2013_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v_a_2024_; uint8_t v___x_2030_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2030_ = l_Lean_LocalDecl_isNondep(v_a_2022_);
if (v___x_2030_ == 0)
{
v_a_2024_ = v___x_2030_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = l_Lean_LocalDecl_type(v_a_2022_);
v___x_2032_ = l_Lean_Meta_isProp(v___x_2031_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; uint8_t v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = lean_unbox(v_a_2033_);
lean_dec(v_a_2033_);
v_a_2024_ = v___x_2034_;
goto v___jp_2023_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v_a_2022_);
lean_dec_ref(v_b_2012_);
v_a_2035_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_2032_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2032_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
v___jp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; 
v___x_2025_ = l_Lean_LocalDecl_setNondep(v_a_2022_, v_a_2024_);
v___x_2026_ = l_Lean_LocalContext_addDecl(v_b_2012_, v___x_2025_);
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2010_, v___x_2027_);
v_i_2010_ = v___x_2028_;
v_b_2012_ = v___x_2026_;
goto _start;
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v_b_2012_);
v_a_2043_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2021_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2021_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_b_2012_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object* v_as_2052_, lean_object* v_i_2053_, lean_object* v_stop_2054_, lean_object* v_b_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
size_t v_i_boxed_2061_; size_t v_stop_boxed_2062_; lean_object* v_res_2063_; 
v_i_boxed_2061_ = lean_unbox_usize(v_i_2053_);
lean_dec(v_i_2053_);
v_stop_boxed_2062_ = lean_unbox_usize(v_stop_2054_);
lean_dec(v_stop_2054_);
v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2052_, v_i_boxed_2061_, v_stop_boxed_2062_, v_b_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec_ref(v_as_2052_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t v_a_2064_, lean_object* v_lctx_2065_, lean_object* v_xs_2066_, lean_object* v_b_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_a_2074_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = lean_array_get_size(v_xs_2066_);
v___x_2083_ = lean_nat_dec_lt(v___x_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
v_a_2074_ = v_lctx_2065_;
goto v___jp_2073_;
}
else
{
size_t v___x_2084_; size_t v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = ((size_t)0ULL);
v___x_2085_ = lean_usize_of_nat(v___x_2082_);
v___x_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2066_, v___x_2084_, v___x_2085_, v_lctx_2065_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v_a_2074_ = v_a_2087_;
goto v___jp_2073_;
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_b_2067_);
lean_dec_ref(v_xs_2066_);
v_a_2088_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2086_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2086_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
v___jp_2073_:
{
uint8_t v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2075_ = 1;
v___x_2076_ = lean_box(v_a_2064_);
v___x_2077_ = lean_box(v_a_2064_);
v___x_2078_ = lean_box(v___x_2075_);
v___x_2079_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2079_, 0, v_xs_2066_);
lean_closure_set(v___x_2079_, 1, v_b_2067_);
lean_closure_set(v___x_2079_, 2, v___x_2076_);
lean_closure_set(v___x_2079_, 3, v___x_2077_);
lean_closure_set(v___x_2079_, 4, v___x_2078_);
v___x_2080_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_a_2074_, v___x_2079_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object* v_a_2096_, lean_object* v_lctx_2097_, lean_object* v_xs_2098_, lean_object* v_b_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
uint8_t v_a_10693__boxed_2105_; lean_object* v_res_2106_; 
v_a_10693__boxed_2105_ = lean_unbox(v_a_2096_);
v_res_2106_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_10693__boxed_2105_, v_lctx_2097_, v_xs_2098_, v_b_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object* v_e_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; 
lean_inc_ref(v_e_2107_);
v___x_2113_ = l_Lean_Meta_isProof(v_e_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2151_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2151_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2151_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_unbox(v_a_2114_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; 
v___x_2119_ = l_Lean_Expr_isLet(v_e_2107_);
if (v___x_2119_ == 0)
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
lean_dec(v_a_2114_);
lean_dec_ref(v_e_2107_);
v___x_2120_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2120_);
v___x_2122_ = v___x_2116_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
else
{
lean_object* v_lctx_2124_; lean_object* v___f_2125_; uint8_t v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
lean_del_object(v___x_2116_);
v_lctx_2124_ = lean_ctor_get(v___y_2108_, 2);
lean_inc_ref(v_lctx_2124_);
lean_inc(v_a_2114_);
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2125_, 0, v_a_2114_);
lean_closure_set(v___f_2125_, 1, v_lctx_2124_);
v___x_2126_ = lean_unbox(v_a_2114_);
v___x_2127_ = lean_unbox(v_a_2114_);
lean_dec(v_a_2114_);
v___x_2128_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2107_, v___f_2125_, v___x_2126_, v___x_2119_, v___x_2127_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2138_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2138_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2138_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_a_2129_);
v___x_2134_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2134_);
v___x_2136_ = v___x_2131_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
v_a_2139_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2128_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2128_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
lean_dec(v_a_2114_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v_e_2107_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2147_);
v___x_2149_ = v___x_2116_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec_ref(v_e_2107_);
v_a_2152_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2113_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2113_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object* v_e_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object* v_00_u03b1_2167_, lean_object* v_x_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = lean_apply_1(v_x_2168_, lean_box(0));
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(v_00_u03b1_2176_, v_x_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2183_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = l_Lean_maxRecDepthErrorMessage;
v___x_2190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
return v___x_2190_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3);
v___x_2192_ = l_Lean_MessageData_ofFormat(v___x_2191_);
return v___x_2192_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4);
v___x_2194_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2));
v___x_2195_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v___x_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object* v_ref_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v_ref_2196_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object* v_ref_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2201_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object* v_x_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___y_2212_; lean_object* v_toCold_2221_; lean_object* v_currRecDepth_2222_; lean_object* v_ref_2223_; uint16_t v_optionFlags_2224_; uint8_t v_suppressElabErrors_2225_; uint8_t v_checkDeprecated_2226_; uint8_t v_isRecordingDeps_2227_; lean_object* v_maxRecDepth_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v_toCold_2221_ = lean_ctor_get(v___y_2208_, 0);
v_currRecDepth_2222_ = lean_ctor_get(v___y_2208_, 1);
v_ref_2223_ = lean_ctor_get(v___y_2208_, 2);
v_optionFlags_2224_ = lean_ctor_get_uint16(v___y_2208_, sizeof(void*)*3);
v_suppressElabErrors_2225_ = lean_ctor_get_uint8(v___y_2208_, sizeof(void*)*3 + 2);
v_checkDeprecated_2226_ = lean_ctor_get_uint8(v___y_2208_, sizeof(void*)*3 + 3);
v_isRecordingDeps_2227_ = lean_ctor_get_uint8(v___y_2208_, sizeof(void*)*3 + 4);
v_maxRecDepth_2233_ = lean_ctor_get(v_toCold_2221_, 3);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_nat_dec_eq(v_maxRecDepth_2233_, v___x_2234_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; 
v___x_2236_ = lean_nat_dec_eq(v_currRecDepth_2222_, v_maxRecDepth_2233_);
if (v___x_2236_ == 0)
{
goto v___jp_2228_;
}
else
{
lean_object* v___x_2237_; 
lean_dec_ref(v_x_2204_);
lean_inc(v_ref_2223_);
v___x_2237_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2223_);
v___y_2212_ = v___x_2237_;
goto v___jp_2211_;
}
}
else
{
goto v___jp_2228_;
}
v___jp_2211_:
{
if (lean_obj_tag(v___y_2212_) == 0)
{
return v___y_2212_;
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
v_a_2213_ = lean_ctor_get(v___y_2212_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___y_2212_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___y_2212_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___y_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
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
v___jp_2228_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2229_ = lean_unsigned_to_nat(1u);
v___x_2230_ = lean_nat_add(v_currRecDepth_2222_, v___x_2229_);
lean_inc(v_ref_2223_);
lean_inc_ref(v_toCold_2221_);
v___x_2231_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_2231_, 0, v_toCold_2221_);
lean_ctor_set(v___x_2231_, 1, v___x_2230_);
lean_ctor_set(v___x_2231_, 2, v_ref_2223_);
lean_ctor_set_uint16(v___x_2231_, sizeof(void*)*3, v_optionFlags_2224_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*3 + 2, v_suppressElabErrors_2225_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*3 + 3, v_checkDeprecated_2226_);
lean_ctor_set_uint8(v___x_2231_, sizeof(void*)*3 + 4, v_isRecordingDeps_2227_);
lean_inc(v___y_2209_);
lean_inc(v___y_2207_);
lean_inc_ref(v___y_2206_);
lean_inc(v___y_2205_);
v___x_2232_ = lean_apply_6(v_x_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___x_2231_, v___y_2209_, lean_box(0));
v___y_2212_ = v___x_2232_;
goto v___jp_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object* v_a_2246_, lean_object* v_x_2247_){
_start:
{
if (lean_obj_tag(v_x_2247_) == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_box(0);
return v___x_2248_;
}
else
{
lean_object* v_key_2249_; lean_object* v_value_2250_; lean_object* v_tail_2251_; uint8_t v___x_2252_; 
v_key_2249_ = lean_ctor_get(v_x_2247_, 0);
v_value_2250_ = lean_ctor_get(v_x_2247_, 1);
v_tail_2251_ = lean_ctor_get(v_x_2247_, 2);
v___x_2252_ = l_Lean_ExprStructEq_beq(v_key_2249_, v_a_2246_);
if (v___x_2252_ == 0)
{
v_x_2247_ = v_tail_2251_;
goto _start;
}
else
{
lean_object* v___x_2254_; 
lean_inc(v_value_2250_);
v___x_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2254_, 0, v_value_2250_);
return v___x_2254_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_a_2255_, lean_object* v_x_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2255_, v_x_2256_);
lean_dec(v_x_2256_);
lean_dec_ref(v_a_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_m_2258_, lean_object* v_a_2259_){
_start:
{
lean_object* v_buckets_2260_; lean_object* v___x_2261_; uint64_t v___x_2262_; uint64_t v___x_2263_; uint64_t v___x_2264_; uint64_t v_fold_2265_; uint64_t v___x_2266_; uint64_t v___x_2267_; uint64_t v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; size_t v___x_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v_buckets_2260_ = lean_ctor_get(v_m_2258_, 1);
v___x_2261_ = lean_array_get_size(v_buckets_2260_);
v___x_2262_ = l_Lean_ExprStructEq_hash(v_a_2259_);
v___x_2263_ = 32ULL;
v___x_2264_ = lean_uint64_shift_right(v___x_2262_, v___x_2263_);
v_fold_2265_ = lean_uint64_xor(v___x_2262_, v___x_2264_);
v___x_2266_ = 16ULL;
v___x_2267_ = lean_uint64_shift_right(v_fold_2265_, v___x_2266_);
v___x_2268_ = lean_uint64_xor(v_fold_2265_, v___x_2267_);
v___x_2269_ = lean_uint64_to_usize(v___x_2268_);
v___x_2270_ = lean_usize_of_nat(v___x_2261_);
v___x_2271_ = ((size_t)1ULL);
v___x_2272_ = lean_usize_sub(v___x_2270_, v___x_2271_);
v___x_2273_ = lean_usize_land(v___x_2269_, v___x_2272_);
v___x_2274_ = lean_array_uget_borrowed(v_buckets_2260_, v___x_2273_);
v___x_2275_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2259_, v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_m_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_2276_, v_a_2277_);
lean_dec_ref(v_a_2277_);
lean_dec_ref(v_m_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2279_, lean_object* v___y_2280_, lean_object* v_b_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; 
lean_inc(v___y_2285_);
lean_inc_ref(v___y_2284_);
lean_inc(v___y_2283_);
lean_inc_ref(v___y_2282_);
lean_inc(v___y_2280_);
v___x_2287_ = lean_apply_7(v_k_2279_, v_b_2281_, v___y_2280_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, lean_box(0));
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2288_, lean_object* v___y_2289_, lean_object* v_b_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2288_, v___y_2289_, v_b_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2289_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2297_, uint8_t v_bi_2298_, lean_object* v_type_2299_, lean_object* v_k_2300_, uint8_t v_kind_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v___f_2308_; lean_object* v___x_2309_; 
lean_inc(v___y_2302_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2308_, 0, v_k_2300_);
lean_closure_set(v___f_2308_, 1, v___y_2302_);
v___x_2309_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2297_, v_bi_2298_, v_type_2299_, v___f_2308_, v_kind_2301_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
if (lean_obj_tag(v___x_2309_) == 0)
{
return v___x_2309_;
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2318_, lean_object* v_bi_2319_, lean_object* v_type_2320_, lean_object* v_k_2321_, lean_object* v_kind_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v_bi_boxed_2329_; uint8_t v_kind_boxed_2330_; lean_object* v_res_2331_; 
v_bi_boxed_2329_ = lean_unbox(v_bi_2319_);
v_kind_boxed_2330_ = lean_unbox(v_kind_2322_);
v_res_2331_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2318_, v_bi_boxed_2329_, v_type_2320_, v_k_2321_, v_kind_boxed_2330_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object* v___x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2332_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2346_, lean_object* v_type_2347_, lean_object* v_val_2348_, lean_object* v_k_2349_, uint8_t v_nondep_2350_, uint8_t v_kind_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___f_2358_; lean_object* v___x_2359_; 
lean_inc(v___y_2352_);
v___f_2358_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2358_, 0, v_k_2349_);
lean_closure_set(v___f_2358_, 1, v___y_2352_);
v___x_2359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2346_, v_type_2347_, v_val_2348_, v___f_2358_, v_nondep_2350_, v_kind_2351_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2359_) == 0)
{
return v___x_2359_;
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2368_, lean_object* v_type_2369_, lean_object* v_val_2370_, lean_object* v_k_2371_, lean_object* v_nondep_2372_, lean_object* v_kind_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
uint8_t v_nondep_boxed_2380_; uint8_t v_kind_boxed_2381_; lean_object* v_res_2382_; 
v_nondep_boxed_2380_ = lean_unbox(v_nondep_2372_);
v_kind_boxed_2381_ = lean_unbox(v_kind_2373_);
v_res_2382_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2368_, v_type_2369_, v_val_2370_, v_k_2371_, v_nondep_boxed_2380_, v_kind_boxed_2381_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = lean_apply_1(v_x_2384_, lean_box(0));
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2392_, v_x_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2400_, lean_object* v_x_2401_){
_start:
{
if (lean_obj_tag(v_x_2401_) == 0)
{
uint8_t v___x_2402_; 
v___x_2402_ = 0;
return v___x_2402_;
}
else
{
lean_object* v_key_2403_; lean_object* v_tail_2404_; uint8_t v___x_2405_; 
v_key_2403_ = lean_ctor_get(v_x_2401_, 0);
v_tail_2404_ = lean_ctor_get(v_x_2401_, 2);
v___x_2405_ = l_Lean_ExprStructEq_beq(v_key_2403_, v_a_2400_);
if (v___x_2405_ == 0)
{
v_x_2401_ = v_tail_2404_;
goto _start;
}
else
{
return v___x_2405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2407_, lean_object* v_x_2408_){
_start:
{
uint8_t v_res_2409_; lean_object* v_r_2410_; 
v_res_2409_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2407_, v_x_2408_);
lean_dec(v_x_2408_);
lean_dec_ref(v_a_2407_);
v_r_2410_ = lean_box(v_res_2409_);
return v_r_2410_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2411_, lean_object* v_b_2412_, lean_object* v_x_2413_){
_start:
{
if (lean_obj_tag(v_x_2413_) == 0)
{
lean_dec(v_b_2412_);
lean_dec_ref(v_a_2411_);
return v_x_2413_;
}
else
{
lean_object* v_key_2414_; lean_object* v_value_2415_; lean_object* v_tail_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2428_; 
v_key_2414_ = lean_ctor_get(v_x_2413_, 0);
v_value_2415_ = lean_ctor_get(v_x_2413_, 1);
v_tail_2416_ = lean_ctor_get(v_x_2413_, 2);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_x_2413_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2418_ = v_x_2413_;
v_isShared_2419_ = v_isSharedCheck_2428_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_tail_2416_);
lean_inc(v_value_2415_);
lean_inc(v_key_2414_);
lean_dec(v_x_2413_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2428_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
uint8_t v___x_2420_; 
v___x_2420_ = l_Lean_ExprStructEq_beq(v_key_2414_, v_a_2411_);
if (v___x_2420_ == 0)
{
lean_object* v___x_2421_; lean_object* v___x_2423_; 
v___x_2421_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2411_, v_b_2412_, v_tail_2416_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 2, v___x_2421_);
v___x_2423_ = v___x_2418_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_key_2414_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_value_2415_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v___x_2421_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
else
{
lean_object* v___x_2426_; 
lean_dec(v_value_2415_);
lean_dec(v_key_2414_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 1, v_b_2412_);
lean_ctor_set(v___x_2418_, 0, v_a_2411_);
v___x_2426_ = v___x_2418_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2411_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_b_2412_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_tail_2416_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2429_, lean_object* v_x_2430_){
_start:
{
if (lean_obj_tag(v_x_2430_) == 0)
{
return v_x_2429_;
}
else
{
lean_object* v_key_2431_; lean_object* v_value_2432_; lean_object* v_tail_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2456_; 
v_key_2431_ = lean_ctor_get(v_x_2430_, 0);
v_value_2432_ = lean_ctor_get(v_x_2430_, 1);
v_tail_2433_ = lean_ctor_get(v_x_2430_, 2);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_x_2430_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2435_ = v_x_2430_;
v_isShared_2436_ = v_isSharedCheck_2456_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_tail_2433_);
lean_inc(v_value_2432_);
lean_inc(v_key_2431_);
lean_dec(v_x_2430_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2456_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; uint64_t v___x_2438_; uint64_t v___x_2439_; uint64_t v___x_2440_; uint64_t v_fold_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; uint64_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; size_t v___x_2448_; size_t v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2437_ = lean_array_get_size(v_x_2429_);
v___x_2438_ = l_Lean_ExprStructEq_hash(v_key_2431_);
v___x_2439_ = 32ULL;
v___x_2440_ = lean_uint64_shift_right(v___x_2438_, v___x_2439_);
v_fold_2441_ = lean_uint64_xor(v___x_2438_, v___x_2440_);
v___x_2442_ = 16ULL;
v___x_2443_ = lean_uint64_shift_right(v_fold_2441_, v___x_2442_);
v___x_2444_ = lean_uint64_xor(v_fold_2441_, v___x_2443_);
v___x_2445_ = lean_uint64_to_usize(v___x_2444_);
v___x_2446_ = lean_usize_of_nat(v___x_2437_);
v___x_2447_ = ((size_t)1ULL);
v___x_2448_ = lean_usize_sub(v___x_2446_, v___x_2447_);
v___x_2449_ = lean_usize_land(v___x_2445_, v___x_2448_);
v___x_2450_ = lean_array_uget_borrowed(v_x_2429_, v___x_2449_);
lean_inc(v___x_2450_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 2, v___x_2450_);
v___x_2452_ = v___x_2435_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_key_2431_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_value_2432_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; 
v___x_2453_ = lean_array_uset(v_x_2429_, v___x_2449_, v___x_2452_);
v_x_2429_ = v___x_2453_;
v_x_2430_ = v_tail_2433_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2457_, lean_object* v_source_2458_, lean_object* v_target_2459_){
_start:
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = lean_array_get_size(v_source_2458_);
v___x_2461_ = lean_nat_dec_lt(v_i_2457_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_dec_ref(v_source_2458_);
lean_dec(v_i_2457_);
return v_target_2459_;
}
else
{
lean_object* v_es_2462_; lean_object* v___x_2463_; lean_object* v_source_2464_; lean_object* v_target_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_es_2462_ = lean_array_fget(v_source_2458_, v_i_2457_);
v___x_2463_ = lean_box(0);
v_source_2464_ = lean_array_fset(v_source_2458_, v_i_2457_, v___x_2463_);
v_target_2465_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2459_, v_es_2462_);
v___x_2466_ = lean_unsigned_to_nat(1u);
v___x_2467_ = lean_nat_add(v_i_2457_, v___x_2466_);
lean_dec(v_i_2457_);
v_i_2457_ = v___x_2467_;
v_source_2458_ = v_source_2464_;
v_target_2459_ = v_target_2465_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2469_){
_start:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_nbuckets_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2470_ = lean_array_get_size(v_data_2469_);
v___x_2471_ = lean_unsigned_to_nat(2u);
v_nbuckets_2472_ = lean_nat_mul(v___x_2470_, v___x_2471_);
v___x_2473_ = lean_unsigned_to_nat(0u);
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_mk_array(v_nbuckets_2472_, v___x_2474_);
v___x_2476_ = lean_array_propagate_mark(v_data_2469_, v___x_2475_);
v___x_2477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2473_, v_data_2469_, v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2478_, lean_object* v_a_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v_size_2481_; lean_object* v_buckets_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2525_; 
v_size_2481_ = lean_ctor_get(v_m_2478_, 0);
v_buckets_2482_ = lean_ctor_get(v_m_2478_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_m_2478_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2484_ = v_m_2478_;
v_isShared_2485_ = v_isSharedCheck_2525_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_buckets_2482_);
lean_inc(v_size_2481_);
lean_dec(v_m_2478_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2525_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; uint64_t v_fold_2490_; uint64_t v___x_2491_; uint64_t v___x_2492_; uint64_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; lean_object* v_bkt_2499_; uint8_t v___x_2500_; 
v___x_2486_ = lean_array_get_size(v_buckets_2482_);
v___x_2487_ = l_Lean_ExprStructEq_hash(v_a_2479_);
v___x_2488_ = 32ULL;
v___x_2489_ = lean_uint64_shift_right(v___x_2487_, v___x_2488_);
v_fold_2490_ = lean_uint64_xor(v___x_2487_, v___x_2489_);
v___x_2491_ = 16ULL;
v___x_2492_ = lean_uint64_shift_right(v_fold_2490_, v___x_2491_);
v___x_2493_ = lean_uint64_xor(v_fold_2490_, v___x_2492_);
v___x_2494_ = lean_uint64_to_usize(v___x_2493_);
v___x_2495_ = lean_usize_of_nat(v___x_2486_);
v___x_2496_ = ((size_t)1ULL);
v___x_2497_ = lean_usize_sub(v___x_2495_, v___x_2496_);
v___x_2498_ = lean_usize_land(v___x_2494_, v___x_2497_);
v_bkt_2499_ = lean_array_uget_borrowed(v_buckets_2482_, v___x_2498_);
v___x_2500_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2479_, v_bkt_2499_);
if (v___x_2500_ == 0)
{
lean_object* v___x_2501_; lean_object* v_size_x27_2502_; lean_object* v___x_2503_; lean_object* v_buckets_x27_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2501_ = lean_unsigned_to_nat(1u);
v_size_x27_2502_ = lean_nat_add(v_size_2481_, v___x_2501_);
lean_dec(v_size_2481_);
lean_inc(v_bkt_2499_);
v___x_2503_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2503_, 0, v_a_2479_);
lean_ctor_set(v___x_2503_, 1, v_b_2480_);
lean_ctor_set(v___x_2503_, 2, v_bkt_2499_);
v_buckets_x27_2504_ = lean_array_uset(v_buckets_2482_, v___x_2498_, v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(4u);
v___x_2506_ = lean_nat_mul(v_size_x27_2502_, v___x_2505_);
v___x_2507_ = lean_unsigned_to_nat(3u);
v___x_2508_ = lean_nat_div(v___x_2506_, v___x_2507_);
lean_dec(v___x_2506_);
v___x_2509_ = lean_array_get_size(v_buckets_x27_2504_);
v___x_2510_ = lean_nat_dec_le(v___x_2508_, v___x_2509_);
lean_dec(v___x_2508_);
if (v___x_2510_ == 0)
{
lean_object* v_val_2511_; lean_object* v___x_2513_; 
v_val_2511_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2504_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v_val_2511_);
lean_ctor_set(v___x_2484_, 0, v_size_x27_2502_);
v___x_2513_ = v___x_2484_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_size_x27_2502_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_val_2511_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
else
{
lean_object* v___x_2516_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v_buckets_x27_2504_);
lean_ctor_set(v___x_2484_, 0, v_size_x27_2502_);
v___x_2516_ = v___x_2484_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_size_x27_2502_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_buckets_x27_2504_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
else
{
lean_object* v___x_2518_; lean_object* v_buckets_x27_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_inc(v_bkt_2499_);
v___x_2518_ = lean_box(0);
v_buckets_x27_2519_ = lean_array_uset(v_buckets_2482_, v___x_2498_, v___x_2518_);
v___x_2520_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2479_, v_b_2480_, v_bkt_2499_);
v___x_2521_ = lean_array_uset(v_buckets_x27_2519_, v___x_2498_, v___x_2520_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 1, v___x_2521_);
v___x_2523_ = v___x_2484_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_size_2481_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2526_, lean_object* v_e_2527_, lean_object* v_a_2528_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2530_ = lean_st_ref_take(v_a_2526_);
v___x_2531_ = lean_box(0);
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2530_, v_e_2527_, v_a_2528_);
v___x_2533_ = lean_st_ref_put(v_a_2526_, v___x_2532_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2534_, lean_object* v_e_2535_, lean_object* v_a_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_res_2538_; 
v_res_2538_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2534_, v_e_2535_, v_a_2536_);
lean_dec(v_a_2534_);
return v_res_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_2539_, lean_object* v_pre_2540_, lean_object* v_post_2541_, lean_object* v_usedLetOnly_2542_, lean_object* v_skipConstInApp_2543_, lean_object* v_skipInstances_2544_, lean_object* v_body_2545_, lean_object* v_x_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
uint8_t v_usedLetOnly_boxed_2553_; uint8_t v_skipConstInApp_boxed_2554_; uint8_t v_skipInstances_boxed_2555_; lean_object* v_res_2556_; 
v_usedLetOnly_boxed_2553_ = lean_unbox(v_usedLetOnly_2542_);
v_skipConstInApp_boxed_2554_ = lean_unbox(v_skipConstInApp_2543_);
v_skipInstances_boxed_2555_ = lean_unbox(v_skipInstances_2544_);
v_res_2556_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_2539_, v_pre_2540_, v_post_2541_, v_usedLetOnly_boxed_2553_, v_skipConstInApp_boxed_2554_, v_skipInstances_boxed_2555_, v_body_2545_, v_x_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
lean_dec(v___y_2549_);
lean_dec_ref(v___y_2548_);
lean_dec(v___y_2547_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2560_, lean_object* v_pre_2561_, lean_object* v_post_2562_, uint8_t v_usedLetOnly_2563_, uint8_t v_skipConstInApp_2564_, uint8_t v_skipInstances_2565_, lean_object* v_body_2566_, lean_object* v_x_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_array_push(v_fvars_2560_, v_x_2567_);
v___x_2575_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2561_, v_post_2562_, v_usedLetOnly_2563_, v_skipConstInApp_2564_, v_skipInstances_2565_, v___x_2574_, v_body_2566_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2576_, lean_object* v_pre_2577_, lean_object* v_post_2578_, lean_object* v_usedLetOnly_2579_, lean_object* v_skipConstInApp_2580_, lean_object* v_skipInstances_2581_, lean_object* v_body_2582_, lean_object* v_x_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
uint8_t v_usedLetOnly_boxed_2590_; uint8_t v_skipConstInApp_boxed_2591_; uint8_t v_skipInstances_boxed_2592_; lean_object* v_res_2593_; 
v_usedLetOnly_boxed_2590_ = lean_unbox(v_usedLetOnly_2579_);
v_skipConstInApp_boxed_2591_ = lean_unbox(v_skipConstInApp_2580_);
v_skipInstances_boxed_2592_ = lean_unbox(v_skipInstances_2581_);
v_res_2593_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2576_, v_pre_2577_, v_post_2578_, v_usedLetOnly_boxed_2590_, v_skipConstInApp_boxed_2591_, v_skipInstances_boxed_2592_, v_body_2582_, v_x_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2594_, lean_object* v_post_2595_, uint8_t v_usedLetOnly_2596_, uint8_t v_skipConstInApp_2597_, uint8_t v_skipInstances_2598_, lean_object* v_e_2599_, lean_object* v_a_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v___x_2606_; 
lean_inc_ref(v_post_2595_);
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc_ref(v_e_2599_);
v___x_2606_ = lean_apply_6(v_post_2595_, v_e_2599_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, lean_box(0));
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2625_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2609_ = v___x_2606_;
v_isShared_2610_ = v_isSharedCheck_2625_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2606_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2625_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
switch(lean_obj_tag(v_a_2607_))
{
case 0:
{
lean_object* v_e_2611_; lean_object* v___x_2613_; 
lean_dec_ref(v_e_2599_);
lean_dec_ref(v_post_2595_);
lean_dec_ref(v_pre_2594_);
v_e_2611_ = lean_ctor_get(v_a_2607_, 0);
lean_inc_ref(v_e_2611_);
lean_dec_ref_known(v_a_2607_, 1);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_e_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_e_2611_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
case 1:
{
lean_object* v_e_2615_; lean_object* v___x_2616_; 
lean_del_object(v___x_2609_);
lean_dec_ref(v_e_2599_);
v_e_2615_ = lean_ctor_get(v_a_2607_, 0);
lean_inc_ref(v_e_2615_);
lean_dec_ref_known(v_a_2607_, 1);
v___x_2616_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2594_, v_post_2595_, v_usedLetOnly_2596_, v_skipConstInApp_2597_, v_skipInstances_2598_, v_e_2615_, v_a_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
return v___x_2616_;
}
default: 
{
lean_object* v_e_x3f_2617_; 
lean_dec_ref(v_post_2595_);
lean_dec_ref(v_pre_2594_);
v_e_x3f_2617_ = lean_ctor_get(v_a_2607_, 0);
lean_inc(v_e_x3f_2617_);
lean_dec_ref_known(v_a_2607_, 1);
if (lean_obj_tag(v_e_x3f_2617_) == 0)
{
lean_object* v___x_2619_; 
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_e_2599_);
v___x_2619_ = v___x_2609_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_e_2599_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
lean_object* v_val_2621_; lean_object* v___x_2623_; 
lean_dec_ref(v_e_2599_);
v_val_2621_ = lean_ctor_get(v_e_x3f_2617_, 0);
lean_inc(v_val_2621_);
lean_dec_ref_known(v_e_x3f_2617_, 1);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 0, v_val_2621_);
v___x_2623_ = v___x_2609_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_val_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
lean_dec_ref(v_e_2599_);
lean_dec_ref(v_post_2595_);
lean_dec_ref(v_pre_2594_);
v_a_2626_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2606_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2606_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2634_, lean_object* v_post_2635_, uint8_t v_usedLetOnly_2636_, uint8_t v_skipConstInApp_2637_, uint8_t v_skipInstances_2638_, lean_object* v_fvars_2639_, lean_object* v_e_2640_, lean_object* v_a_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
if (lean_obj_tag(v_e_2640_) == 6)
{
lean_object* v_binderName_2647_; lean_object* v_binderType_2648_; lean_object* v_body_2649_; uint8_t v_binderInfo_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v_binderName_2647_ = lean_ctor_get(v_e_2640_, 0);
lean_inc(v_binderName_2647_);
v_binderType_2648_ = lean_ctor_get(v_e_2640_, 1);
lean_inc_ref(v_binderType_2648_);
v_body_2649_ = lean_ctor_get(v_e_2640_, 2);
lean_inc_ref(v_body_2649_);
v_binderInfo_2650_ = lean_ctor_get_uint8(v_e_2640_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_2640_, 3);
v___x_2651_ = lean_box(v_usedLetOnly_2636_);
v___x_2652_ = lean_box(v_skipConstInApp_2637_);
v___x_2653_ = lean_box(v_skipInstances_2638_);
lean_inc_ref(v_post_2635_);
lean_inc_ref(v_pre_2634_);
lean_inc_ref(v_fvars_2639_);
v___f_2654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2654_, 0, v_fvars_2639_);
lean_closure_set(v___f_2654_, 1, v_pre_2634_);
lean_closure_set(v___f_2654_, 2, v_post_2635_);
lean_closure_set(v___f_2654_, 3, v___x_2651_);
lean_closure_set(v___f_2654_, 4, v___x_2652_);
lean_closure_set(v___f_2654_, 5, v___x_2653_);
lean_closure_set(v___f_2654_, 6, v_body_2649_);
v___x_2655_ = lean_expr_instantiate_rev(v_binderType_2648_, v_fvars_2639_);
lean_dec_ref(v_fvars_2639_);
lean_dec_ref(v_binderType_2648_);
v___x_2656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2634_, v_post_2635_, v_usedLetOnly_2636_, v_skipConstInApp_2637_, v_skipInstances_2638_, v___x_2655_, v_a_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; uint8_t v___x_2658_; lean_object* v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
v___x_2658_ = 0;
v___x_2659_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2647_, v_binderInfo_2650_, v_a_2657_, v___f_2654_, v___x_2658_, v_a_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2659_;
}
else
{
lean_dec_ref(v___f_2654_);
lean_dec(v_binderName_2647_);
return v___x_2656_;
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_expr_instantiate_rev(v_e_2640_, v_fvars_2639_);
lean_dec_ref(v_e_2640_);
lean_inc_ref(v_post_2635_);
lean_inc_ref(v_pre_2634_);
v___x_2661_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2634_, v_post_2635_, v_usedLetOnly_2636_, v_skipConstInApp_2637_, v_skipInstances_2638_, v___x_2660_, v_a_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; uint8_t v___x_2663_; uint8_t v___x_2664_; uint8_t v___x_2665_; lean_object* v___x_2666_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = 0;
v___x_2664_ = 1;
v___x_2665_ = 1;
v___x_2666_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2639_, v_a_2662_, v___x_2663_, v_usedLetOnly_2636_, v___x_2663_, v___x_2664_, v___x_2665_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec_ref(v_fvars_2639_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2634_, v_post_2635_, v_usedLetOnly_2636_, v_skipConstInApp_2637_, v_skipInstances_2638_, v_a_2667_, v_a_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
return v___x_2668_;
}
else
{
lean_dec_ref(v_post_2635_);
lean_dec_ref(v_pre_2634_);
return v___x_2666_;
}
}
else
{
lean_dec_ref(v_fvars_2639_);
lean_dec_ref(v_post_2635_);
lean_dec_ref(v_pre_2634_);
return v___x_2661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2669_, lean_object* v_pre_2670_, lean_object* v_post_2671_, uint8_t v_usedLetOnly_2672_, uint8_t v_skipConstInApp_2673_, uint8_t v_skipInstances_2674_, lean_object* v_body_2675_, lean_object* v_x_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_array_push(v_fvars_2669_, v_x_2676_);
v___x_2684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2670_, v_post_2671_, v_usedLetOnly_2672_, v_skipConstInApp_2673_, v_skipInstances_2674_, v___x_2683_, v_body_2675_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2685_, lean_object* v_pre_2686_, lean_object* v_post_2687_, lean_object* v_usedLetOnly_2688_, lean_object* v_skipConstInApp_2689_, lean_object* v_skipInstances_2690_, lean_object* v_body_2691_, lean_object* v_x_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v_usedLetOnly_boxed_2699_; uint8_t v_skipConstInApp_boxed_2700_; uint8_t v_skipInstances_boxed_2701_; lean_object* v_res_2702_; 
v_usedLetOnly_boxed_2699_ = lean_unbox(v_usedLetOnly_2688_);
v_skipConstInApp_boxed_2700_ = lean_unbox(v_skipConstInApp_2689_);
v_skipInstances_boxed_2701_ = lean_unbox(v_skipInstances_2690_);
v_res_2702_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2685_, v_pre_2686_, v_post_2687_, v_usedLetOnly_boxed_2699_, v_skipConstInApp_boxed_2700_, v_skipInstances_boxed_2701_, v_body_2691_, v_x_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2703_, lean_object* v_post_2704_, uint8_t v_usedLetOnly_2705_, uint8_t v_skipConstInApp_2706_, uint8_t v_skipInstances_2707_, lean_object* v_fvars_2708_, lean_object* v_e_2709_, lean_object* v_a_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
if (lean_obj_tag(v_e_2709_) == 8)
{
lean_object* v_declName_2716_; lean_object* v_type_2717_; lean_object* v_value_2718_; lean_object* v_body_2719_; uint8_t v_nondep_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___f_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v_declName_2716_ = lean_ctor_get(v_e_2709_, 0);
lean_inc(v_declName_2716_);
v_type_2717_ = lean_ctor_get(v_e_2709_, 1);
lean_inc_ref(v_type_2717_);
v_value_2718_ = lean_ctor_get(v_e_2709_, 2);
lean_inc_ref(v_value_2718_);
v_body_2719_ = lean_ctor_get(v_e_2709_, 3);
lean_inc_ref(v_body_2719_);
v_nondep_2720_ = lean_ctor_get_uint8(v_e_2709_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_2709_, 4);
v___x_2721_ = lean_box(v_usedLetOnly_2705_);
v___x_2722_ = lean_box(v_skipConstInApp_2706_);
v___x_2723_ = lean_box(v_skipInstances_2707_);
lean_inc_ref_n(v_post_2704_, 2);
lean_inc_ref_n(v_pre_2703_, 2);
lean_inc_ref(v_fvars_2708_);
v___f_2724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2724_, 0, v_fvars_2708_);
lean_closure_set(v___f_2724_, 1, v_pre_2703_);
lean_closure_set(v___f_2724_, 2, v_post_2704_);
lean_closure_set(v___f_2724_, 3, v___x_2721_);
lean_closure_set(v___f_2724_, 4, v___x_2722_);
lean_closure_set(v___f_2724_, 5, v___x_2723_);
lean_closure_set(v___f_2724_, 6, v_body_2719_);
v___x_2725_ = lean_expr_instantiate_rev(v_type_2717_, v_fvars_2708_);
lean_dec_ref(v_type_2717_);
v___x_2726_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2703_, v_post_2704_, v_usedLetOnly_2705_, v_skipConstInApp_2706_, v_skipInstances_2707_, v___x_2725_, v_a_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___x_2728_ = lean_expr_instantiate_rev(v_value_2718_, v_fvars_2708_);
lean_dec_ref(v_fvars_2708_);
lean_dec_ref(v_value_2718_);
v___x_2729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2703_, v_post_2704_, v_usedLetOnly_2705_, v_skipConstInApp_2706_, v_skipInstances_2707_, v___x_2728_, v_a_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; uint8_t v___x_2731_; lean_object* v___x_2732_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
v___x_2731_ = 0;
v___x_2732_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2716_, v_a_2727_, v_a_2730_, v___f_2724_, v_nondep_2720_, v___x_2731_, v_a_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
return v___x_2732_;
}
else
{
lean_dec(v_a_2727_);
lean_dec_ref(v___f_2724_);
lean_dec(v_declName_2716_);
return v___x_2729_;
}
}
else
{
lean_dec_ref(v___f_2724_);
lean_dec_ref(v_value_2718_);
lean_dec(v_declName_2716_);
lean_dec_ref(v_fvars_2708_);
lean_dec_ref(v_post_2704_);
lean_dec_ref(v_pre_2703_);
return v___x_2726_;
}
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_expr_instantiate_rev(v_e_2709_, v_fvars_2708_);
lean_dec_ref(v_e_2709_);
lean_inc_ref(v_post_2704_);
lean_inc_ref(v_pre_2703_);
v___x_2734_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2703_, v_post_2704_, v_usedLetOnly_2705_, v_skipConstInApp_2706_, v_skipInstances_2707_, v___x_2733_, v_a_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; uint8_t v___x_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = 0;
v___x_2737_ = 1;
v___x_2738_ = l_Lean_Meta_mkLetFVars(v_fvars_2708_, v_a_2735_, v_usedLetOnly_2705_, v___x_2736_, v___x_2737_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec_ref(v_fvars_2708_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2740_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
v___x_2740_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2703_, v_post_2704_, v_usedLetOnly_2705_, v_skipConstInApp_2706_, v_skipInstances_2707_, v_a_2739_, v_a_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
return v___x_2740_;
}
else
{
lean_dec_ref(v_post_2704_);
lean_dec_ref(v_pre_2703_);
return v___x_2738_;
}
}
else
{
lean_dec_ref(v_fvars_2708_);
lean_dec_ref(v_post_2704_);
lean_dec_ref(v_pre_2703_);
return v___x_2734_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_pre_2741_, lean_object* v_post_2742_, uint8_t v_usedLetOnly_2743_, uint8_t v_skipConstInApp_2744_, uint8_t v_skipInstances_2745_, size_t v_sz_2746_, size_t v_i_2747_, lean_object* v_bs_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
uint8_t v___x_2755_; 
v___x_2755_ = lean_usize_dec_lt(v_i_2747_, v_sz_2746_);
if (v___x_2755_ == 0)
{
lean_object* v___x_2756_; 
lean_dec_ref(v_post_2742_);
lean_dec_ref(v_pre_2741_);
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_bs_2748_);
return v___x_2756_;
}
else
{
lean_object* v_v_2757_; lean_object* v___x_2758_; lean_object* v_bs_x27_2759_; lean_object* v___x_2760_; 
v_v_2757_ = lean_array_uget(v_bs_2748_, v_i_2747_);
v___x_2758_ = lean_unsigned_to_nat(0u);
v_bs_x27_2759_ = lean_array_uset(v_bs_2748_, v_i_2747_, v___x_2758_);
lean_inc_ref(v_post_2742_);
lean_inc_ref(v_pre_2741_);
v___x_2760_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2741_, v_post_2742_, v_usedLetOnly_2743_, v_skipConstInApp_2744_, v_skipInstances_2745_, v_v_2757_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; size_t v___x_2762_; size_t v___x_2763_; lean_object* v___x_2764_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v___x_2762_ = ((size_t)1ULL);
v___x_2763_ = lean_usize_add(v_i_2747_, v___x_2762_);
v___x_2764_ = lean_array_uset(v_bs_x27_2759_, v_i_2747_, v_a_2761_);
v_i_2747_ = v___x_2763_;
v_bs_2748_ = v___x_2764_;
goto _start;
}
else
{
lean_object* v_a_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2773_; 
lean_dec_ref(v_bs_x27_2759_);
lean_dec_ref(v_post_2742_);
lean_dec_ref(v_pre_2741_);
v_a_2766_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2768_ = v___x_2760_;
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_a_2766_);
lean_dec(v___x_2760_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2773_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2771_; 
if (v_isShared_2769_ == 0)
{
v___x_2771_ = v___x_2768_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_a_2766_);
v___x_2771_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
return v___x_2771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_2774_, lean_object* v_post_2775_, uint8_t v_usedLetOnly_2776_, uint8_t v_skipConstInApp_2777_, uint8_t v_skipInstances_2778_, lean_object* v___x_2779_, lean_object* v___y_2780_, lean_object* v_b_2781_, lean_object* v_a_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2774_, v_post_2775_, v_usedLetOnly_2776_, v_skipConstInApp_2777_, v_skipInstances_2778_, v___x_2779_, v___y_2780_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2798_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2798_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_array_fset(v_b_2781_, v_a_2782_, v_a_2789_);
v___x_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2794_);
v___x_2796_ = v___x_2791_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_dec_ref(v_b_2781_);
v_a_2799_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2788_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2788_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_2807_, lean_object* v_post_2808_, lean_object* v_usedLetOnly_2809_, lean_object* v_skipConstInApp_2810_, lean_object* v_skipInstances_2811_, lean_object* v___x_2812_, lean_object* v___y_2813_, lean_object* v_b_2814_, lean_object* v_a_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
uint8_t v_usedLetOnly_boxed_2821_; uint8_t v_skipConstInApp_boxed_2822_; uint8_t v_skipInstances_boxed_2823_; lean_object* v_res_2824_; 
v_usedLetOnly_boxed_2821_ = lean_unbox(v_usedLetOnly_2809_);
v_skipConstInApp_boxed_2822_ = lean_unbox(v_skipConstInApp_2810_);
v_skipInstances_boxed_2823_ = lean_unbox(v_skipInstances_2811_);
v_res_2824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2807_, v_post_2808_, v_usedLetOnly_boxed_2821_, v_skipConstInApp_boxed_2822_, v_skipInstances_boxed_2823_, v___x_2812_, v___y_2813_, v_b_2814_, v_a_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
lean_dec(v___y_2817_);
lean_dec_ref(v___y_2816_);
lean_dec(v_a_2815_);
lean_dec(v___y_2813_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object* v_upperBound_2825_, lean_object* v___x_2826_, lean_object* v_pre_2827_, lean_object* v_post_2828_, uint8_t v_usedLetOnly_2829_, uint8_t v_skipConstInApp_2830_, uint8_t v_skipInstances_2831_, lean_object* v_a_2832_, lean_object* v_b_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v___y_2841_; uint8_t v___x_2864_; 
v___x_2864_ = lean_nat_dec_lt(v_a_2832_, v_upperBound_2825_);
if (v___x_2864_ == 0)
{
lean_object* v___x_2865_; 
lean_dec(v_a_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v___x_2865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2865_, 0, v_b_2833_);
return v___x_2865_;
}
else
{
lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2866_ = lean_array_fget_borrowed(v_b_2833_, v_a_2832_);
v___x_2867_ = lean_array_get_size(v___x_2826_);
v___x_2868_ = lean_nat_dec_lt(v_a_2832_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___f_2872_; 
lean_inc(v___x_2866_);
v___x_2869_ = lean_box(v_usedLetOnly_2829_);
v___x_2870_ = lean_box(v_skipConstInApp_2830_);
v___x_2871_ = lean_box(v_skipInstances_2831_);
lean_inc(v_a_2832_);
lean_inc(v___y_2834_);
lean_inc_ref(v_post_2828_);
lean_inc_ref(v_pre_2827_);
v___f_2872_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2872_, 0, v_pre_2827_);
lean_closure_set(v___f_2872_, 1, v_post_2828_);
lean_closure_set(v___f_2872_, 2, v___x_2869_);
lean_closure_set(v___f_2872_, 3, v___x_2870_);
lean_closure_set(v___f_2872_, 4, v___x_2871_);
lean_closure_set(v___f_2872_, 5, v___x_2866_);
lean_closure_set(v___f_2872_, 6, v___y_2834_);
lean_closure_set(v___f_2872_, 7, v_b_2833_);
lean_closure_set(v___f_2872_, 8, v_a_2832_);
v___y_2841_ = v___f_2872_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2873_; uint8_t v_isInstance_2874_; 
v___x_2873_ = lean_array_fget_borrowed(v___x_2826_, v_a_2832_);
v_isInstance_2874_ = lean_ctor_get_uint8(v___x_2873_, sizeof(void*)*1 + 4);
if (v_isInstance_2874_ == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___f_2878_; 
lean_inc(v___x_2866_);
v___x_2875_ = lean_box(v_usedLetOnly_2829_);
v___x_2876_ = lean_box(v_skipConstInApp_2830_);
v___x_2877_ = lean_box(v_skipInstances_2831_);
lean_inc(v_a_2832_);
lean_inc(v___y_2834_);
lean_inc_ref(v_post_2828_);
lean_inc_ref(v_pre_2827_);
v___f_2878_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2878_, 0, v_pre_2827_);
lean_closure_set(v___f_2878_, 1, v_post_2828_);
lean_closure_set(v___f_2878_, 2, v___x_2875_);
lean_closure_set(v___f_2878_, 3, v___x_2876_);
lean_closure_set(v___f_2878_, 4, v___x_2877_);
lean_closure_set(v___f_2878_, 5, v___x_2866_);
lean_closure_set(v___f_2878_, 6, v___y_2834_);
lean_closure_set(v___f_2878_, 7, v_b_2833_);
lean_closure_set(v___f_2878_, 8, v_a_2832_);
v___y_2841_ = v___f_2878_;
goto v___jp_2840_;
}
else
{
lean_object* v___x_2879_; lean_object* v___f_2880_; 
v___x_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2879_, 0, v_b_2833_);
v___f_2880_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2880_, 0, v___x_2879_);
v___y_2841_ = v___f_2880_;
goto v___jp_2840_;
}
}
}
v___jp_2840_:
{
lean_object* v___x_2842_; 
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
v___x_2842_ = lean_apply_5(v___y_2841_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, lean_box(0));
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2855_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2855_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2855_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
if (lean_obj_tag(v_a_2843_) == 0)
{
lean_object* v_a_2847_; lean_object* v___x_2849_; 
lean_dec(v_a_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_a_2847_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v_a_2843_, 1);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v_a_2847_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2847_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_del_object(v___x_2845_);
v_a_2851_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v_a_2843_, 1);
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = lean_nat_add(v_a_2832_, v___x_2852_);
lean_dec(v_a_2832_);
v_a_2832_ = v___x_2853_;
v_b_2833_ = v_a_2851_;
goto _start;
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2832_);
lean_dec_ref(v_post_2828_);
lean_dec_ref(v_pre_2827_);
v_a_2856_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2842_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2842_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2881_, lean_object* v_pre_2882_, lean_object* v_post_2883_, uint8_t v_usedLetOnly_2884_, uint8_t v_skipConstInApp_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_, lean_object* v_x_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_f_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; 
if (lean_obj_tag(v_x_2886_) == 5)
{
lean_object* v_fn_2944_; lean_object* v_arg_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_fn_2944_ = lean_ctor_get(v_x_2886_, 0);
lean_inc_ref(v_fn_2944_);
v_arg_2945_ = lean_ctor_get(v_x_2886_, 1);
lean_inc_ref(v_arg_2945_);
lean_dec_ref_known(v_x_2886_, 2);
v___x_2946_ = lean_array_set(v_x_2887_, v_x_2888_, v_arg_2945_);
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = lean_nat_sub(v_x_2888_, v___x_2947_);
lean_dec(v_x_2888_);
v_x_2886_ = v_fn_2944_;
v_x_2887_ = v___x_2946_;
v_x_2888_ = v___x_2948_;
goto _start;
}
else
{
lean_dec(v_x_2888_);
if (v_skipConstInApp_2885_ == 0)
{
goto v___jp_2941_;
}
else
{
uint8_t v___x_2950_; 
v___x_2950_ = l_Lean_Expr_isConst(v_x_2886_);
if (v___x_2950_ == 0)
{
goto v___jp_2941_;
}
else
{
v_f_2896_ = v_x_2886_;
v___y_2897_ = v___y_2889_;
v___y_2898_ = v___y_2890_;
v___y_2899_ = v___y_2891_;
v___y_2900_ = v___y_2892_;
v___y_2901_ = v___y_2893_;
goto v___jp_2895_;
}
}
}
v___jp_2895_:
{
if (v_skipInstances_2881_ == 0)
{
size_t v_sz_2902_; size_t v___x_2903_; lean_object* v___x_2904_; 
v_sz_2902_ = lean_array_size(v_x_2887_);
v___x_2903_ = ((size_t)0ULL);
lean_inc_ref(v_post_2883_);
lean_inc_ref(v_pre_2882_);
v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2882_, v_post_2883_, v_usedLetOnly_2884_, v_skipConstInApp_2885_, v_skipInstances_2881_, v_sz_2902_, v___x_2903_, v_x_2887_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = l_Lean_mkAppN(v_f_2896_, v_a_2905_);
lean_dec(v_a_2905_);
v___x_2907_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2882_, v_post_2883_, v_usedLetOnly_2884_, v_skipConstInApp_2885_, v_skipInstances_2881_, v___x_2906_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2907_;
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v_f_2896_);
lean_dec_ref(v_post_2883_);
lean_dec_ref(v_pre_2882_);
v_a_2908_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2904_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2904_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = lean_array_get_size(v_x_2887_);
lean_inc_ref(v_f_2896_);
v___x_2917_ = l_Lean_Meta_getFunInfoNArgs(v_f_2896_, v___x_2916_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v_paramInfo_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
v_paramInfo_2919_ = lean_ctor_get(v_a_2918_, 0);
lean_inc_ref(v_paramInfo_2919_);
lean_dec(v_a_2918_);
v___x_2920_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2883_);
lean_inc_ref(v_pre_2882_);
v___x_2921_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v___x_2916_, v_paramInfo_2919_, v_pre_2882_, v_post_2883_, v_usedLetOnly_2884_, v_skipConstInApp_2885_, v_skipInstances_2881_, v___x_2920_, v_x_2887_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
lean_dec_ref(v_paramInfo_2919_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = l_Lean_mkAppN(v_f_2896_, v_a_2922_);
lean_dec(v_a_2922_);
v___x_2924_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2882_, v_post_2883_, v_usedLetOnly_2884_, v_skipConstInApp_2885_, v_skipInstances_2881_, v___x_2923_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_, v___y_2901_);
return v___x_2924_;
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v_f_2896_);
lean_dec_ref(v_post_2883_);
lean_dec_ref(v_pre_2882_);
v_a_2925_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2921_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2921_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v_f_2896_);
lean_dec_ref(v_x_2887_);
lean_dec_ref(v_post_2883_);
lean_dec_ref(v_pre_2882_);
v_a_2933_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2917_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2917_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
}
v___jp_2941_:
{
lean_object* v___x_2942_; 
lean_inc_ref(v_post_2883_);
lean_inc_ref(v_pre_2882_);
v___x_2942_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2882_, v_post_2883_, v_usedLetOnly_2884_, v_skipConstInApp_2885_, v_skipInstances_2881_, v_x_2886_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_object* v_a_2943_; 
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref_known(v___x_2942_, 1);
v_f_2896_ = v_a_2943_;
v___y_2897_ = v___y_2889_;
v___y_2898_ = v___y_2890_;
v___y_2899_ = v___y_2891_;
v___y_2900_ = v___y_2892_;
v___y_2901_ = v___y_2893_;
goto v___jp_2895_;
}
else
{
lean_dec_ref(v_x_2887_);
lean_dec_ref(v_post_2883_);
lean_dec_ref(v_pre_2882_);
return v___x_2942_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v___x_2951_, lean_object* v_pre_2952_, lean_object* v_e_2953_, lean_object* v_post_2954_, uint8_t v_usedLetOnly_2955_, uint8_t v_skipConstInApp_2956_, uint8_t v_skipInstances_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v___x_2964_; 
v___x_2964_ = l_Lean_Core_checkSystem(v___x_2951_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; 
lean_dec_ref_known(v___x_2964_, 1);
lean_inc_ref(v_pre_2952_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
lean_inc(v___y_2960_);
lean_inc_ref(v___y_2959_);
lean_inc_ref(v_e_2953_);
v___x_2965_ = lean_apply_6(v_pre_2952_, v_e_2953_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, lean_box(0));
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3014_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_3014_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3014_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___y_2971_; 
switch(lean_obj_tag(v_a_2966_))
{
case 0:
{
lean_object* v_e_3006_; lean_object* v___x_3008_; 
lean_dec_ref(v_post_2954_);
lean_dec_ref(v_e_2953_);
lean_dec_ref(v_pre_2952_);
v_e_3006_ = lean_ctor_get(v_a_2966_, 0);
lean_inc_ref(v_e_3006_);
lean_dec_ref_known(v_a_2966_, 1);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 0, v_e_3006_);
v___x_3008_ = v___x_2968_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_e_3006_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
case 1:
{
lean_object* v_e_3010_; lean_object* v___x_3011_; 
lean_del_object(v___x_2968_);
lean_dec_ref(v_e_2953_);
v_e_3010_ = lean_ctor_get(v_a_2966_, 0);
lean_inc_ref(v_e_3010_);
lean_dec_ref_known(v_a_2966_, 1);
v___x_3011_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v_e_3010_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_3011_;
}
default: 
{
lean_object* v_e_x3f_3012_; 
lean_del_object(v___x_2968_);
v_e_x3f_3012_ = lean_ctor_get(v_a_2966_, 0);
lean_inc(v_e_x3f_3012_);
lean_dec_ref_known(v_a_2966_, 1);
if (lean_obj_tag(v_e_x3f_3012_) == 0)
{
v___y_2971_ = v_e_2953_;
goto v___jp_2970_;
}
else
{
lean_object* v_val_3013_; 
lean_dec_ref(v_e_2953_);
v_val_3013_ = lean_ctor_get(v_e_x3f_3012_, 0);
lean_inc(v_val_3013_);
lean_dec_ref_known(v_e_x3f_3012_, 1);
v___y_2971_ = v_val_3013_;
goto v___jp_2970_;
}
}
}
v___jp_2970_:
{
switch(lean_obj_tag(v___y_2971_))
{
case 7:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2973_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___x_2972_, v___y_2971_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2973_;
}
case 6:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2974_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2975_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___x_2974_, v___y_2971_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2975_;
}
case 8:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2977_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___x_2976_, v___y_2971_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2977_;
}
case 5:
{
lean_object* v_dummy_2978_; lean_object* v_nargs_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; 
v_dummy_2978_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_2979_ = l_Lean_Expr_getAppNumArgs(v___y_2971_);
lean_inc(v_nargs_2979_);
v___x_2980_ = lean_mk_array(v_nargs_2979_, v_dummy_2978_);
v___x_2981_ = lean_unsigned_to_nat(1u);
v___x_2982_ = lean_nat_sub(v_nargs_2979_, v___x_2981_);
lean_dec(v_nargs_2979_);
v___x_2983_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_2957_, v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v___y_2971_, v___x_2980_, v___x_2982_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2983_;
}
case 10:
{
lean_object* v_data_2984_; lean_object* v_expr_2985_; lean_object* v___x_2986_; 
v_data_2984_ = lean_ctor_get(v___y_2971_, 0);
v_expr_2985_ = lean_ctor_get(v___y_2971_, 1);
lean_inc_ref(v_expr_2985_);
lean_inc_ref(v_post_2954_);
lean_inc_ref(v_pre_2952_);
v___x_2986_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v_expr_2985_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; size_t v___x_2988_; size_t v___x_2989_; uint8_t v___x_2990_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = lean_ptr_addr(v_expr_2985_);
v___x_2989_ = lean_ptr_addr(v_a_2987_);
v___x_2990_ = lean_usize_dec_eq(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_inc(v_data_2984_);
lean_dec_ref_known(v___y_2971_, 2);
v___x_2991_ = l_Lean_Expr_mdata___override(v_data_2984_, v_a_2987_);
v___x_2992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___x_2991_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; 
lean_dec(v_a_2987_);
v___x_2993_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___y_2971_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_2993_;
}
}
else
{
lean_dec_ref_known(v___y_2971_, 2);
lean_dec_ref(v_post_2954_);
lean_dec_ref(v_pre_2952_);
return v___x_2986_;
}
}
case 11:
{
lean_object* v_typeName_2994_; lean_object* v_idx_2995_; lean_object* v_struct_2996_; lean_object* v___x_2997_; 
v_typeName_2994_ = lean_ctor_get(v___y_2971_, 0);
v_idx_2995_ = lean_ctor_get(v___y_2971_, 1);
v_struct_2996_ = lean_ctor_get(v___y_2971_, 2);
lean_inc_ref(v_struct_2996_);
lean_inc_ref(v_post_2954_);
lean_inc_ref(v_pre_2952_);
v___x_2997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v_struct_2996_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; size_t v___x_2999_; size_t v___x_3000_; uint8_t v___x_3001_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_ptr_addr(v_struct_2996_);
v___x_3000_ = lean_ptr_addr(v_a_2998_);
v___x_3001_ = lean_usize_dec_eq(v___x_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_inc(v_idx_2995_);
lean_inc(v_typeName_2994_);
lean_dec_ref_known(v___y_2971_, 3);
v___x_3002_ = l_Lean_Expr_proj___override(v_typeName_2994_, v_idx_2995_, v_a_2998_);
v___x_3003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___x_3002_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; 
lean_dec(v_a_2998_);
v___x_3004_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___y_2971_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_3004_;
}
}
else
{
lean_dec_ref_known(v___y_2971_, 3);
lean_dec_ref(v_post_2954_);
lean_dec_ref(v_pre_2952_);
return v___x_2997_;
}
}
default: 
{
lean_object* v___x_3005_; 
v___x_3005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2952_, v_post_2954_, v_usedLetOnly_2955_, v_skipConstInApp_2956_, v_skipInstances_2957_, v___y_2971_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
return v___x_3005_;
}
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_post_2954_);
lean_dec_ref(v_e_2953_);
lean_dec_ref(v_pre_2952_);
v_a_3015_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2965_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2965_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec_ref(v_post_2954_);
lean_dec_ref(v_e_2953_);
lean_dec_ref(v_pre_2952_);
v_a_3023_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2964_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2964_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v___x_3031_, lean_object* v_pre_3032_, lean_object* v_e_3033_, lean_object* v_post_3034_, lean_object* v_usedLetOnly_3035_, lean_object* v_skipConstInApp_3036_, lean_object* v_skipInstances_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
uint8_t v_usedLetOnly_boxed_3044_; uint8_t v_skipConstInApp_boxed_3045_; uint8_t v_skipInstances_boxed_3046_; lean_object* v_res_3047_; 
v_usedLetOnly_boxed_3044_ = lean_unbox(v_usedLetOnly_3035_);
v_skipConstInApp_boxed_3045_ = lean_unbox(v_skipConstInApp_3036_);
v_skipInstances_boxed_3046_ = lean_unbox(v_skipInstances_3037_);
v_res_3047_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v___x_3031_, v_pre_3032_, v_e_3033_, v_post_3034_, v_usedLetOnly_boxed_3044_, v_skipConstInApp_boxed_3045_, v_skipInstances_boxed_3046_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3048_, lean_object* v_post_3049_, uint8_t v_usedLetOnly_3050_, uint8_t v_skipConstInApp_3051_, uint8_t v_skipInstances_3052_, lean_object* v_e_3053_, lean_object* v_a_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
lean_inc(v_a_3054_);
v___x_3060_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3060_, 0, lean_box(0));
lean_closure_set(v___x_3060_, 1, lean_box(0));
lean_closure_set(v___x_3060_, 2, v_a_3054_);
v___x_3061_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3060_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3096_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3096_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3096_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3062_, v_e_3053_);
lean_dec(v_a_3062_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___f_3071_; lean_object* v___x_3072_; 
lean_del_object(v___x_3064_);
v___x_3067_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
v___x_3068_ = lean_box(v_usedLetOnly_3050_);
v___x_3069_ = lean_box(v_skipConstInApp_3051_);
v___x_3070_ = lean_box(v_skipInstances_3052_);
lean_inc_ref(v_e_3053_);
v___f_3071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3071_, 0, v___x_3067_);
lean_closure_set(v___f_3071_, 1, v_pre_3048_);
lean_closure_set(v___f_3071_, 2, v_e_3053_);
lean_closure_set(v___f_3071_, 3, v_post_3049_);
lean_closure_set(v___f_3071_, 4, v___x_3068_);
lean_closure_set(v___f_3071_, 5, v___x_3069_);
lean_closure_set(v___f_3071_, 6, v___x_3070_);
v___x_3072_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3071_, v_a_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___f_3074_; lean_object* v___x_3075_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc_n(v_a_3073_, 2);
lean_dec_ref_known(v___x_3072_, 1);
lean_inc(v_a_3054_);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3074_, 0, v_a_3054_);
lean_closure_set(v___f_3074_, 1, v_e_3053_);
lean_closure_set(v___f_3074_, 2, v_a_3073_);
v___x_3075_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3074_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3082_ == 0)
{
lean_object* v_unused_3083_; 
v_unused_3083_ = lean_ctor_get(v___x_3075_, 0);
lean_dec(v_unused_3083_);
v___x_3077_ = v___x_3075_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_dec(v___x_3075_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v_a_3073_);
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3073_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_3073_);
v_a_3084_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3075_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3075_);
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
lean_dec_ref(v_e_3053_);
return v___x_3072_;
}
}
else
{
lean_object* v_val_3092_; lean_object* v___x_3094_; 
lean_dec_ref(v_e_3053_);
lean_dec_ref(v_post_3049_);
lean_dec_ref(v_pre_3048_);
v_val_3092_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3066_, 1);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v_val_3092_);
v___x_3094_ = v___x_3064_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_val_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v_e_3053_);
lean_dec_ref(v_post_3049_);
lean_dec_ref(v_pre_3048_);
v_a_3097_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3061_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3061_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3105_, lean_object* v_post_3106_, uint8_t v_usedLetOnly_3107_, uint8_t v_skipConstInApp_3108_, uint8_t v_skipInstances_3109_, lean_object* v_fvars_3110_, lean_object* v_e_3111_, lean_object* v_a_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_){
_start:
{
if (lean_obj_tag(v_e_3111_) == 7)
{
lean_object* v_binderName_3118_; lean_object* v_binderType_3119_; lean_object* v_body_3120_; uint8_t v_binderInfo_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___f_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_binderName_3118_ = lean_ctor_get(v_e_3111_, 0);
lean_inc(v_binderName_3118_);
v_binderType_3119_ = lean_ctor_get(v_e_3111_, 1);
lean_inc_ref(v_binderType_3119_);
v_body_3120_ = lean_ctor_get(v_e_3111_, 2);
lean_inc_ref(v_body_3120_);
v_binderInfo_3121_ = lean_ctor_get_uint8(v_e_3111_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3111_, 3);
v___x_3122_ = lean_box(v_usedLetOnly_3107_);
v___x_3123_ = lean_box(v_skipConstInApp_3108_);
v___x_3124_ = lean_box(v_skipInstances_3109_);
lean_inc_ref(v_post_3106_);
lean_inc_ref(v_pre_3105_);
lean_inc_ref(v_fvars_3110_);
v___f_3125_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3125_, 0, v_fvars_3110_);
lean_closure_set(v___f_3125_, 1, v_pre_3105_);
lean_closure_set(v___f_3125_, 2, v_post_3106_);
lean_closure_set(v___f_3125_, 3, v___x_3122_);
lean_closure_set(v___f_3125_, 4, v___x_3123_);
lean_closure_set(v___f_3125_, 5, v___x_3124_);
lean_closure_set(v___f_3125_, 6, v_body_3120_);
v___x_3126_ = lean_expr_instantiate_rev(v_binderType_3119_, v_fvars_3110_);
lean_dec_ref(v_fvars_3110_);
lean_dec_ref(v_binderType_3119_);
v___x_3127_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3105_, v_post_3106_, v_usedLetOnly_3107_, v_skipConstInApp_3108_, v_skipInstances_3109_, v___x_3126_, v_a_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; uint8_t v___x_3129_; lean_object* v___x_3130_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
lean_inc(v_a_3128_);
lean_dec_ref_known(v___x_3127_, 1);
v___x_3129_ = 0;
v___x_3130_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3118_, v_binderInfo_3121_, v_a_3128_, v___f_3125_, v___x_3129_, v_a_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
return v___x_3130_;
}
else
{
lean_dec_ref(v___f_3125_);
lean_dec(v_binderName_3118_);
return v___x_3127_;
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_expr_instantiate_rev(v_e_3111_, v_fvars_3110_);
lean_dec_ref(v_e_3111_);
lean_inc_ref(v_post_3106_);
lean_inc_ref(v_pre_3105_);
v___x_3132_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3105_, v_post_3106_, v_usedLetOnly_3107_, v_skipConstInApp_3108_, v_skipInstances_3109_, v___x_3131_, v_a_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3132_) == 0)
{
lean_object* v_a_3133_; uint8_t v___x_3134_; uint8_t v___x_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; 
v_a_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_a_3133_);
lean_dec_ref_known(v___x_3132_, 1);
v___x_3134_ = 0;
v___x_3135_ = 1;
v___x_3136_ = 1;
v___x_3137_ = l_Lean_Meta_mkForallFVars(v_fvars_3110_, v_a_3133_, v___x_3134_, v_usedLetOnly_3107_, v___x_3135_, v___x_3136_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec_ref(v_fvars_3110_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3139_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
v___x_3139_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3105_, v_post_3106_, v_usedLetOnly_3107_, v_skipConstInApp_3108_, v_skipInstances_3109_, v_a_3138_, v_a_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
return v___x_3139_;
}
else
{
lean_dec_ref(v_post_3106_);
lean_dec_ref(v_pre_3105_);
return v___x_3137_;
}
}
else
{
lean_dec_ref(v_fvars_3110_);
lean_dec_ref(v_post_3106_);
lean_dec_ref(v_pre_3105_);
return v___x_3132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3140_, lean_object* v_pre_3141_, lean_object* v_post_3142_, uint8_t v_usedLetOnly_3143_, uint8_t v_skipConstInApp_3144_, uint8_t v_skipInstances_3145_, lean_object* v_body_3146_, lean_object* v_x_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_array_push(v_fvars_3140_, v_x_3147_);
v___x_3155_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3141_, v_post_3142_, v_usedLetOnly_3143_, v_skipConstInApp_3144_, v_skipInstances_3145_, v___x_3154_, v_body_3146_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3156_, lean_object* v_post_3157_, lean_object* v_usedLetOnly_3158_, lean_object* v_skipConstInApp_3159_, lean_object* v_skipInstances_3160_, lean_object* v_e_3161_, lean_object* v_a_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
uint8_t v_usedLetOnly_boxed_3168_; uint8_t v_skipConstInApp_boxed_3169_; uint8_t v_skipInstances_boxed_3170_; lean_object* v_res_3171_; 
v_usedLetOnly_boxed_3168_ = lean_unbox(v_usedLetOnly_3158_);
v_skipConstInApp_boxed_3169_ = lean_unbox(v_skipConstInApp_3159_);
v_skipInstances_boxed_3170_ = lean_unbox(v_skipInstances_3160_);
v_res_3171_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3156_, v_post_3157_, v_usedLetOnly_boxed_3168_, v_skipConstInApp_boxed_3169_, v_skipInstances_boxed_3170_, v_e_3161_, v_a_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v_a_3162_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_pre_3172_, lean_object* v_post_3173_, lean_object* v_usedLetOnly_3174_, lean_object* v_skipConstInApp_3175_, lean_object* v_skipInstances_3176_, lean_object* v_sz_3177_, lean_object* v_i_3178_, lean_object* v_bs_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_usedLetOnly_boxed_3186_; uint8_t v_skipConstInApp_boxed_3187_; uint8_t v_skipInstances_boxed_3188_; size_t v_sz_boxed_3189_; size_t v_i_boxed_3190_; lean_object* v_res_3191_; 
v_usedLetOnly_boxed_3186_ = lean_unbox(v_usedLetOnly_3174_);
v_skipConstInApp_boxed_3187_ = lean_unbox(v_skipConstInApp_3175_);
v_skipInstances_boxed_3188_ = lean_unbox(v_skipInstances_3176_);
v_sz_boxed_3189_ = lean_unbox_usize(v_sz_3177_);
lean_dec(v_sz_3177_);
v_i_boxed_3190_ = lean_unbox_usize(v_i_3178_);
lean_dec(v_i_3178_);
v_res_3191_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_3172_, v_post_3173_, v_usedLetOnly_boxed_3186_, v_skipConstInApp_boxed_3187_, v_skipInstances_boxed_3188_, v_sz_boxed_3189_, v_i_boxed_3190_, v_bs_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3192_, lean_object* v_post_3193_, lean_object* v_usedLetOnly_3194_, lean_object* v_skipConstInApp_3195_, lean_object* v_skipInstances_3196_, lean_object* v_e_3197_, lean_object* v_a_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
uint8_t v_usedLetOnly_boxed_3204_; uint8_t v_skipConstInApp_boxed_3205_; uint8_t v_skipInstances_boxed_3206_; lean_object* v_res_3207_; 
v_usedLetOnly_boxed_3204_ = lean_unbox(v_usedLetOnly_3194_);
v_skipConstInApp_boxed_3205_ = lean_unbox(v_skipConstInApp_3195_);
v_skipInstances_boxed_3206_ = lean_unbox(v_skipInstances_3196_);
v_res_3207_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3192_, v_post_3193_, v_usedLetOnly_boxed_3204_, v_skipConstInApp_boxed_3205_, v_skipInstances_boxed_3206_, v_e_3197_, v_a_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v_a_3198_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3208_, lean_object* v_post_3209_, lean_object* v_usedLetOnly_3210_, lean_object* v_skipConstInApp_3211_, lean_object* v_skipInstances_3212_, lean_object* v_fvars_3213_, lean_object* v_e_3214_, lean_object* v_a_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
uint8_t v_usedLetOnly_boxed_3221_; uint8_t v_skipConstInApp_boxed_3222_; uint8_t v_skipInstances_boxed_3223_; lean_object* v_res_3224_; 
v_usedLetOnly_boxed_3221_ = lean_unbox(v_usedLetOnly_3210_);
v_skipConstInApp_boxed_3222_ = lean_unbox(v_skipConstInApp_3211_);
v_skipInstances_boxed_3223_ = lean_unbox(v_skipInstances_3212_);
v_res_3224_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3208_, v_post_3209_, v_usedLetOnly_boxed_3221_, v_skipConstInApp_boxed_3222_, v_skipInstances_boxed_3223_, v_fvars_3213_, v_e_3214_, v_a_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v_a_3215_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3225_, lean_object* v_post_3226_, lean_object* v_usedLetOnly_3227_, lean_object* v_skipConstInApp_3228_, lean_object* v_skipInstances_3229_, lean_object* v_fvars_3230_, lean_object* v_e_3231_, lean_object* v_a_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_usedLetOnly_boxed_3238_; uint8_t v_skipConstInApp_boxed_3239_; uint8_t v_skipInstances_boxed_3240_; lean_object* v_res_3241_; 
v_usedLetOnly_boxed_3238_ = lean_unbox(v_usedLetOnly_3227_);
v_skipConstInApp_boxed_3239_ = lean_unbox(v_skipConstInApp_3228_);
v_skipInstances_boxed_3240_ = lean_unbox(v_skipInstances_3229_);
v_res_3241_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3225_, v_post_3226_, v_usedLetOnly_boxed_3238_, v_skipConstInApp_boxed_3239_, v_skipInstances_boxed_3240_, v_fvars_3230_, v_e_3231_, v_a_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v_a_3232_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3242_, lean_object* v_post_3243_, lean_object* v_usedLetOnly_3244_, lean_object* v_skipConstInApp_3245_, lean_object* v_skipInstances_3246_, lean_object* v_fvars_3247_, lean_object* v_e_3248_, lean_object* v_a_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_){
_start:
{
uint8_t v_usedLetOnly_boxed_3255_; uint8_t v_skipConstInApp_boxed_3256_; uint8_t v_skipInstances_boxed_3257_; lean_object* v_res_3258_; 
v_usedLetOnly_boxed_3255_ = lean_unbox(v_usedLetOnly_3244_);
v_skipConstInApp_boxed_3256_ = lean_unbox(v_skipConstInApp_3245_);
v_skipInstances_boxed_3257_ = lean_unbox(v_skipInstances_3246_);
v_res_3258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3242_, v_post_3243_, v_usedLetOnly_boxed_3255_, v_skipConstInApp_boxed_3256_, v_skipInstances_boxed_3257_, v_fvars_3247_, v_e_3248_, v_a_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v_a_3249_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3259_, lean_object* v___x_3260_, lean_object* v_pre_3261_, lean_object* v_post_3262_, lean_object* v_usedLetOnly_3263_, lean_object* v_skipConstInApp_3264_, lean_object* v_skipInstances_3265_, lean_object* v_a_3266_, lean_object* v_b_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v_usedLetOnly_boxed_3274_; uint8_t v_skipConstInApp_boxed_3275_; uint8_t v_skipInstances_boxed_3276_; lean_object* v_res_3277_; 
v_usedLetOnly_boxed_3274_ = lean_unbox(v_usedLetOnly_3263_);
v_skipConstInApp_boxed_3275_ = lean_unbox(v_skipConstInApp_3264_);
v_skipInstances_boxed_3276_ = lean_unbox(v_skipInstances_3265_);
v_res_3277_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3259_, v___x_3260_, v_pre_3261_, v_post_3262_, v_usedLetOnly_boxed_3274_, v_skipConstInApp_boxed_3275_, v_skipInstances_boxed_3276_, v_a_3266_, v_b_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___x_3260_);
lean_dec(v_upperBound_3259_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3278_, lean_object* v_pre_3279_, lean_object* v_post_3280_, lean_object* v_usedLetOnly_3281_, lean_object* v_skipConstInApp_3282_, lean_object* v_x_3283_, lean_object* v_x_3284_, lean_object* v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
uint8_t v_skipInstances_boxed_3292_; uint8_t v_usedLetOnly_boxed_3293_; uint8_t v_skipConstInApp_boxed_3294_; lean_object* v_res_3295_; 
v_skipInstances_boxed_3292_ = lean_unbox(v_skipInstances_3278_);
v_usedLetOnly_boxed_3293_ = lean_unbox(v_usedLetOnly_3281_);
v_skipConstInApp_boxed_3294_ = lean_unbox(v_skipConstInApp_3282_);
v_res_3295_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3292_, v_pre_3279_, v_post_3280_, v_usedLetOnly_boxed_3293_, v_skipConstInApp_boxed_3294_, v_x_3283_, v_x_3284_, v_x_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
return v_res_3295_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_unsigned_to_nat(16u);
v___x_3298_ = lean_mk_array(v___x_3297_, v___x_3296_);
return v___x_3298_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0);
v___x_3300_ = lean_unsigned_to_nat(0u);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3299_);
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3302_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3303_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3303_, 0, lean_box(0));
lean_closure_set(v___x_3303_, 1, lean_box(0));
lean_closure_set(v___x_3303_, 2, v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3304_, lean_object* v_pre_3305_, lean_object* v_post_3306_, uint8_t v_usedLetOnly_3307_, uint8_t v_skipConstInApp_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
uint8_t v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v_a_3317_; lean_object* v___x_3318_; 
v___x_3314_ = 0;
v___x_3315_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3316_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3315_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref(v___x_3316_);
v___x_3318_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3305_, v_post_3306_, v_usedLetOnly_3307_, v_skipConstInApp_3308_, v___x_3314_, v_input_3304_, v_a_3317_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3320_, 0, lean_box(0));
lean_closure_set(v___x_3320_, 1, lean_box(0));
lean_closure_set(v___x_3320_, 2, v_a_3317_);
v___x_3321_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3320_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3328_ == 0)
{
lean_object* v_unused_3329_; 
v_unused_3329_ = lean_ctor_get(v___x_3321_, 0);
lean_dec(v_unused_3329_);
v___x_3323_ = v___x_3321_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_dec(v___x_3321_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 0, v_a_3319_);
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3319_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
else
{
lean_dec(v_a_3317_);
return v___x_3318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3330_, lean_object* v_pre_3331_, lean_object* v_post_3332_, lean_object* v_usedLetOnly_3333_, lean_object* v_skipConstInApp_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
uint8_t v_usedLetOnly_boxed_3340_; uint8_t v_skipConstInApp_boxed_3341_; lean_object* v_res_3342_; 
v_usedLetOnly_boxed_3340_ = lean_unbox(v_usedLetOnly_3333_);
v_skipConstInApp_boxed_3341_ = lean_unbox(v_skipConstInApp_3334_);
v_res_3342_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3330_, v_pre_3331_, v_post_3332_, v_usedLetOnly_boxed_3340_, v_skipConstInApp_boxed_3341_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v___f_3351_; lean_object* v___f_3352_; uint8_t v___x_3353_; lean_object* v___x_3354_; 
v___f_3351_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3353_ = 0;
v___x_3354_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3345_, v___f_3352_, v___f_3351_, v___x_3353_, v___x_3353_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_upperBound_3362_, lean_object* v___x_3363_, lean_object* v_pre_3364_, lean_object* v_post_3365_, uint8_t v_usedLetOnly_3366_, uint8_t v_skipConstInApp_3367_, uint8_t v_skipInstances_3368_, lean_object* v___x_3369_, lean_object* v_inst_3370_, lean_object* v_R_3371_, lean_object* v_a_3372_, lean_object* v_b_3373_, lean_object* v_c_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3362_, v___x_3363_, v_pre_3364_, v_post_3365_, v_usedLetOnly_3366_, v_skipConstInApp_3367_, v_skipInstances_3368_, v_a_3372_, v_b_3373_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_3382_ = _args[0];
lean_object* v___x_3383_ = _args[1];
lean_object* v_pre_3384_ = _args[2];
lean_object* v_post_3385_ = _args[3];
lean_object* v_usedLetOnly_3386_ = _args[4];
lean_object* v_skipConstInApp_3387_ = _args[5];
lean_object* v_skipInstances_3388_ = _args[6];
lean_object* v___x_3389_ = _args[7];
lean_object* v_inst_3390_ = _args[8];
lean_object* v_R_3391_ = _args[9];
lean_object* v_a_3392_ = _args[10];
lean_object* v_b_3393_ = _args[11];
lean_object* v_c_3394_ = _args[12];
lean_object* v___y_3395_ = _args[13];
lean_object* v___y_3396_ = _args[14];
lean_object* v___y_3397_ = _args[15];
lean_object* v___y_3398_ = _args[16];
lean_object* v___y_3399_ = _args[17];
lean_object* v___y_3400_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3401_; uint8_t v_skipConstInApp_boxed_3402_; uint8_t v_skipInstances_boxed_3403_; lean_object* v_res_3404_; 
v_usedLetOnly_boxed_3401_ = lean_unbox(v_usedLetOnly_3386_);
v_skipConstInApp_boxed_3402_ = lean_unbox(v_skipConstInApp_3387_);
v_skipInstances_boxed_3403_ = lean_unbox(v_skipInstances_3388_);
v_res_3404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3382_, v___x_3383_, v_pre_3384_, v_post_3385_, v_usedLetOnly_boxed_3401_, v_skipConstInApp_boxed_3402_, v_skipInstances_boxed_3403_, v___x_3389_, v_inst_3390_, v_R_3391_, v_a_3392_, v_b_3393_, v_c_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec(v___x_3389_);
lean_dec_ref(v___x_3383_);
lean_dec(v_upperBound_3382_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_00_u03b2_3405_, lean_object* v_m_3406_, lean_object* v_a_3407_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_3406_, v_a_3407_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3409_, lean_object* v_m_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_00_u03b2_3409_, v_m_3410_, v_a_3411_);
lean_dec_ref(v_a_3411_);
lean_dec_ref(v_m_3410_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3413_, lean_object* v_name_3414_, uint8_t v_bi_3415_, lean_object* v_type_3416_, lean_object* v_k_3417_, uint8_t v_kind_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v___x_3425_; 
v___x_3425_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3414_, v_bi_3415_, v_type_3416_, v_k_3417_, v_kind_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3426_, lean_object* v_name_3427_, lean_object* v_bi_3428_, lean_object* v_type_3429_, lean_object* v_k_3430_, lean_object* v_kind_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
uint8_t v_bi_boxed_3438_; uint8_t v_kind_boxed_3439_; lean_object* v_res_3440_; 
v_bi_boxed_3438_ = lean_unbox(v_bi_3428_);
v_kind_boxed_3439_ = lean_unbox(v_kind_3431_);
v_res_3440_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3426_, v_name_3427_, v_bi_boxed_3438_, v_type_3429_, v_k_3430_, v_kind_boxed_3439_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3441_, lean_object* v_name_3442_, lean_object* v_type_3443_, lean_object* v_val_3444_, lean_object* v_k_3445_, uint8_t v_nondep_3446_, uint8_t v_kind_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3442_, v_type_3443_, v_val_3444_, v_k_3445_, v_nondep_3446_, v_kind_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3455_, lean_object* v_name_3456_, lean_object* v_type_3457_, lean_object* v_val_3458_, lean_object* v_k_3459_, lean_object* v_nondep_3460_, lean_object* v_kind_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v_nondep_boxed_3468_; uint8_t v_kind_boxed_3469_; lean_object* v_res_3470_; 
v_nondep_boxed_3468_ = lean_unbox(v_nondep_3460_);
v_kind_boxed_3469_ = lean_unbox(v_kind_3461_);
v_res_3470_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3455_, v_name_3456_, v_type_3457_, v_val_3458_, v_k_3459_, v_nondep_boxed_3468_, v_kind_boxed_3469_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3471_, lean_object* v_ref_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3472_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3479_, lean_object* v_ref_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3479_, v_ref_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3487_, lean_object* v_x_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3488_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3496_, lean_object* v_x_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3496_, v_x_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3505_, lean_object* v_m_3506_, lean_object* v_a_3507_, lean_object* v_b_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3506_, v_a_3507_, v_b_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3510_, lean_object* v_a_3511_, lean_object* v_x_3512_){
_start:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_3511_, v_x_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b2_3514_, lean_object* v_a_3515_, lean_object* v_x_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(v_00_u03b2_3514_, v_a_3515_, v_x_3516_);
lean_dec(v_x_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3518_, lean_object* v_a_3519_, lean_object* v_x_3520_){
_start:
{
uint8_t v___x_3521_; 
v___x_3521_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3519_, v_x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3522_, lean_object* v_a_3523_, lean_object* v_x_3524_){
_start:
{
uint8_t v_res_3525_; lean_object* v_r_3526_; 
v_res_3525_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3522_, v_a_3523_, v_x_3524_);
lean_dec(v_x_3524_);
lean_dec_ref(v_a_3523_);
v_r_3526_ = lean_box(v_res_3525_);
return v_r_3526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3527_, lean_object* v_data_3528_){
_start:
{
lean_object* v___x_3529_; 
v___x_3529_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3528_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3530_, lean_object* v_a_3531_, lean_object* v_b_3532_, lean_object* v_x_3533_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3531_, v_b_3532_, v_x_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3535_, lean_object* v_i_3536_, lean_object* v_source_3537_, lean_object* v_target_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3536_, v_source_3537_, v_target_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3540_, lean_object* v_x_3541_, lean_object* v_x_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3541_, v_x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3544_, lean_object* v_opt_3545_){
_start:
{
lean_object* v_name_3546_; lean_object* v_defValue_3547_; lean_object* v_map_3548_; lean_object* v___x_3549_; 
v_name_3546_ = lean_ctor_get(v_opt_3545_, 0);
v_defValue_3547_ = lean_ctor_get(v_opt_3545_, 1);
v_map_3548_ = lean_ctor_get(v_opts_3544_, 0);
v___x_3549_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3548_, v_name_3546_);
if (lean_obj_tag(v___x_3549_) == 0)
{
uint8_t v___x_3550_; 
v___x_3550_ = lean_unbox(v_defValue_3547_);
return v___x_3550_;
}
else
{
lean_object* v_val_3551_; 
v_val_3551_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_val_3551_);
lean_dec_ref_known(v___x_3549_, 1);
if (lean_obj_tag(v_val_3551_) == 1)
{
uint8_t v_v_3552_; 
v_v_3552_ = lean_ctor_get_uint8(v_val_3551_, 0);
lean_dec_ref_known(v_val_3551_, 0);
return v_v_3552_;
}
else
{
uint8_t v___x_3553_; 
lean_dec(v_val_3551_);
v___x_3553_ = lean_unbox(v_defValue_3547_);
return v___x_3553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3554_, lean_object* v_opt_3555_){
_start:
{
uint8_t v_res_3556_; lean_object* v_r_3557_; 
v_res_3556_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3554_, v_opt_3555_);
lean_dec_ref(v_opt_3555_);
lean_dec_ref(v_opts_3554_);
v_r_3557_ = lean_box(v_res_3556_);
return v_r_3557_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg(){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___closed__0);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg___boxed(lean_object* v___dummy_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
return v_res_3563_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___redArg();
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(lean_object* v_e_3567_, lean_object* v_k_3568_, uint8_t v_cleanupAnnotations_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v___f_3575_; uint8_t v___x_3576_; uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3575_, 0, v_k_3568_);
v___x_3576_ = 1;
v___x_3577_ = 0;
v___x_3578_ = lean_box(0);
v___x_3579_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3567_, v___x_3576_, v___x_3577_, v___x_3576_, v___x_3577_, v___x_3578_, v___f_3575_, v_cleanupAnnotations_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3587_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3582_ = v___x_3579_;
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_a_3580_);
lean_dec(v___x_3579_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3587_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___x_3585_; 
if (v_isShared_3583_ == 0)
{
v___x_3585_ = v___x_3582_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v_a_3580_);
v___x_3585_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
return v___x_3585_;
}
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
v_a_3588_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3579_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3579_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg___boxed(lean_object* v_e_3596_, lean_object* v_k_3597_, lean_object* v_cleanupAnnotations_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3604_; lean_object* v_res_3605_; 
v_cleanupAnnotations_boxed_3604_ = lean_unbox(v_cleanupAnnotations_3598_);
v_res_3605_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3596_, v_k_3597_, v_cleanupAnnotations_boxed_3604_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_00_u03b1_3606_, lean_object* v_e_3607_, lean_object* v_k_3608_, uint8_t v_cleanupAnnotations_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3607_, v_k_3608_, v_cleanupAnnotations_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_00_u03b1_3616_, lean_object* v_e_3617_, lean_object* v_k_3618_, lean_object* v_cleanupAnnotations_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3625_; lean_object* v_res_3626_; 
v_cleanupAnnotations_boxed_3625_ = lean_unbox(v_cleanupAnnotations_3619_);
v_res_3626_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(v_00_u03b1_3616_, v_e_3617_, v_k_3618_, v_cleanupAnnotations_boxed_3625_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___y_3621_);
lean_dec_ref(v___y_3620_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_){
_start:
{
if (lean_obj_tag(v_x_3627_) == 5)
{
lean_object* v_fn_3634_; lean_object* v_arg_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_fn_3634_ = lean_ctor_get(v_x_3627_, 0);
lean_inc_ref(v_fn_3634_);
v_arg_3635_ = lean_ctor_get(v_x_3627_, 1);
lean_inc_ref(v_arg_3635_);
lean_dec_ref_known(v_x_3627_, 2);
v___x_3636_ = lean_array_set(v_x_3628_, v_x_3629_, v_arg_3635_);
v___x_3637_ = lean_unsigned_to_nat(1u);
v___x_3638_ = lean_nat_sub(v_x_3629_, v___x_3637_);
lean_dec(v_x_3629_);
v_x_3627_ = v_fn_3634_;
v_x_3628_ = v___x_3636_;
v_x_3629_ = v___x_3638_;
goto _start;
}
else
{
lean_object* v___x_3640_; uint8_t v___x_3641_; 
lean_dec(v_x_3629_);
v___x_3640_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3641_ = l_Lean_Expr_isConstOf(v_x_3627_, v___x_3640_);
lean_dec_ref(v_x_3627_);
if (v___x_3641_ == 0)
{
lean_dec_ref(v_x_3628_);
goto v___jp_3631_;
}
else
{
lean_object* v___x_3642_; lean_object* v___x_3643_; uint8_t v___x_3644_; 
v___x_3642_ = lean_unsigned_to_nat(2u);
v___x_3643_ = lean_array_get_size(v_x_3628_);
v___x_3644_ = lean_nat_dec_le(v___x_3642_, v___x_3643_);
if (v___x_3644_ == 0)
{
lean_dec_ref(v_x_3628_);
goto v___jp_3631_;
}
else
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3645_ = lean_unsigned_to_nat(1u);
v___x_3646_ = lean_array_fget(v_x_3628_, v___x_3645_);
v___x_3647_ = l_Array_toSubarray___redArg(v_x_3628_, v___x_3642_, v___x_3643_);
v___x_3648_ = l_Subarray_copy___redArg(v___x_3647_);
v___x_3649_ = l_Lean_mkAppN(v___x_3646_, v___x_3648_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
v___x_3652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
return v___x_3652_;
}
}
}
v___jp_3631_:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
return v___x_3633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3653_, v_x_3654_, v_x_3655_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(lean_object* v_e_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_dummy_3664_; lean_object* v_nargs_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_dummy_3664_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3665_ = l_Lean_Expr_getAppNumArgs(v_e_3658_);
lean_inc(v_nargs_3665_);
v___x_3666_ = lean_mk_array(v_nargs_3665_, v_dummy_3664_);
v___x_3667_ = lean_unsigned_to_nat(1u);
v___x_3668_ = lean_nat_sub(v_nargs_3665_, v___x_3667_);
lean_dec(v_nargs_3665_);
v___x_3669_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3658_, v___x_3666_, v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v_e_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Lean_Elab_WF_preprocess___lam__0(v_e_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
return v_res_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(lean_object* v_ref_3677_){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3679_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v_ref_3677_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_ref_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_res_3684_; 
v_res_3684_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3682_);
return v_res_3684_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = lean_box(0);
v___x_3686_ = l_Lean_interruptExceptionId;
v___x_3687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
lean_ctor_set(v___x_3687_, 1, v___x_3685_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg(){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___closed__0);
v___x_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
return v___x_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg___boxed(lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(lean_object* v_x_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___y_3701_; uint8_t v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; uint16_t v___y_3714_; uint8_t v___y_3715_; lean_object* v___y_3716_; uint8_t v___y_3717_; lean_object* v_toCold_3722_; lean_object* v_currRecDepth_3723_; lean_object* v_ref_3724_; uint16_t v_optionFlags_3725_; uint8_t v_suppressElabErrors_3726_; uint8_t v_checkDeprecated_3727_; uint8_t v_isRecordingDeps_3728_; lean_object* v_maxRecDepth_3729_; lean_object* v_cancelTk_x3f_3730_; 
v_toCold_3722_ = lean_ctor_get(v___y_3697_, 0);
v_currRecDepth_3723_ = lean_ctor_get(v___y_3697_, 1);
v_ref_3724_ = lean_ctor_get(v___y_3697_, 2);
v_optionFlags_3725_ = lean_ctor_get_uint16(v___y_3697_, sizeof(void*)*3);
v_suppressElabErrors_3726_ = lean_ctor_get_uint8(v___y_3697_, sizeof(void*)*3 + 2);
v_checkDeprecated_3727_ = lean_ctor_get_uint8(v___y_3697_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3728_ = lean_ctor_get_uint8(v___y_3697_, sizeof(void*)*3 + 4);
v_maxRecDepth_3729_ = lean_ctor_get(v_toCold_3722_, 3);
v_cancelTk_x3f_3730_ = lean_ctor_get(v_toCold_3722_, 10);
if (lean_obj_tag(v_cancelTk_x3f_3730_) == 1)
{
lean_object* v_val_3736_; uint8_t v___x_3737_; 
v_val_3736_ = lean_ctor_get(v_cancelTk_x3f_3730_, 0);
v___x_3737_ = l_IO_CancelToken_isSet(v_val_3736_);
if (v___x_3737_ == 0)
{
goto v___jp_3731_;
}
else
{
lean_object* v___x_3738_; lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec_ref(v_x_3693_);
v___x_3738_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
goto v___jp_3731_;
}
v___jp_3700_:
{
if (lean_obj_tag(v___y_3701_) == 0)
{
return v___y_3701_;
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v_a_3702_ = lean_ctor_get(v___y_3701_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___y_3701_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___y_3701_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___y_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
v___jp_3710_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3718_ = lean_unsigned_to_nat(1u);
v___x_3719_ = lean_nat_add(v___y_3716_, v___x_3718_);
lean_inc_ref(v___y_3712_);
v___x_3720_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3720_, 0, v___y_3712_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
lean_ctor_set(v___x_3720_, 2, v___y_3713_);
lean_ctor_set_uint16(v___x_3720_, sizeof(void*)*3, v___y_3714_);
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*3 + 2, v___y_3711_);
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*3 + 3, v___y_3717_);
lean_ctor_set_uint8(v___x_3720_, sizeof(void*)*3 + 4, v___y_3715_);
lean_inc(v___y_3698_);
lean_inc(v___y_3696_);
lean_inc_ref(v___y_3695_);
lean_inc(v___y_3694_);
v___x_3721_ = lean_apply_6(v_x_3693_, v___y_3694_, v___y_3695_, v___y_3696_, v___x_3720_, v___y_3698_, lean_box(0));
v___y_3701_ = v___x_3721_;
goto v___jp_3700_;
}
v___jp_3731_:
{
lean_object* v___x_3732_; uint8_t v___x_3733_; 
v___x_3732_ = lean_unsigned_to_nat(0u);
v___x_3733_ = lean_nat_dec_eq(v_maxRecDepth_3729_, v___x_3732_);
if (v___x_3733_ == 0)
{
uint8_t v___x_3734_; 
v___x_3734_ = lean_nat_dec_eq(v_currRecDepth_3723_, v_maxRecDepth_3729_);
if (v___x_3734_ == 0)
{
lean_inc(v_ref_3724_);
v___y_3711_ = v_suppressElabErrors_3726_;
v___y_3712_ = v_toCold_3722_;
v___y_3713_ = v_ref_3724_;
v___y_3714_ = v_optionFlags_3725_;
v___y_3715_ = v_isRecordingDeps_3728_;
v___y_3716_ = v_currRecDepth_3723_;
v___y_3717_ = v_checkDeprecated_3727_;
goto v___jp_3710_;
}
else
{
lean_object* v___x_3735_; 
lean_dec_ref(v_x_3693_);
lean_inc(v_ref_3724_);
v___x_3735_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3724_);
v___y_3701_ = v___x_3735_;
goto v___jp_3700_;
}
}
else
{
lean_inc(v_ref_3724_);
v___y_3711_ = v_suppressElabErrors_3726_;
v___y_3712_ = v_toCold_3722_;
v___y_3713_ = v_ref_3724_;
v___y_3714_ = v_optionFlags_3725_;
v___y_3715_ = v_isRecordingDeps_3728_;
v___y_3716_ = v_currRecDepth_3723_;
v___y_3717_ = v_checkDeprecated_3727_;
goto v___jp_3710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg___boxed(lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(lean_object* v_pre_3755_, lean_object* v_post_3756_, size_t v_sz_3757_, size_t v_i_3758_, lean_object* v_bs_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v___x_3766_; 
v___x_3766_ = lean_usize_dec_lt(v_i_3758_, v_sz_3757_);
if (v___x_3766_ == 0)
{
lean_object* v___x_3767_; 
lean_dec_ref(v_post_3756_);
lean_dec_ref(v_pre_3755_);
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v_bs_3759_);
return v___x_3767_;
}
else
{
lean_object* v_v_3768_; lean_object* v___x_3769_; lean_object* v_bs_x27_3770_; lean_object* v___x_3771_; 
v_v_3768_ = lean_array_uget(v_bs_3759_, v_i_3758_);
v___x_3769_ = lean_unsigned_to_nat(0u);
v_bs_x27_3770_ = lean_array_uset(v_bs_3759_, v_i_3758_, v___x_3769_);
lean_inc_ref(v_post_3756_);
lean_inc_ref(v_pre_3755_);
v___x_3771_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3755_, v_post_3756_, v_v_3768_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; size_t v___x_3773_; size_t v___x_3774_; lean_object* v___x_3775_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = ((size_t)1ULL);
v___x_3774_ = lean_usize_add(v_i_3758_, v___x_3773_);
v___x_3775_ = lean_array_uset(v_bs_x27_3770_, v_i_3758_, v_a_3772_);
v_i_3758_ = v___x_3774_;
v_bs_3759_ = v___x_3775_;
goto _start;
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v_bs_x27_3770_);
lean_dec_ref(v_post_3756_);
lean_dec_ref(v_pre_3755_);
v_a_3777_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3771_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3771_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_3785_, lean_object* v_post_3786_, lean_object* v_x_3787_, lean_object* v_x_3788_, lean_object* v_x_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
if (lean_obj_tag(v_x_3787_) == 5)
{
lean_object* v_fn_3796_; lean_object* v_arg_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; 
v_fn_3796_ = lean_ctor_get(v_x_3787_, 0);
lean_inc_ref(v_fn_3796_);
v_arg_3797_ = lean_ctor_get(v_x_3787_, 1);
lean_inc_ref(v_arg_3797_);
lean_dec_ref_known(v_x_3787_, 2);
v___x_3798_ = lean_array_set(v_x_3788_, v_x_3789_, v_arg_3797_);
v___x_3799_ = lean_unsigned_to_nat(1u);
v___x_3800_ = lean_nat_sub(v_x_3789_, v___x_3799_);
lean_dec(v_x_3789_);
v_x_3787_ = v_fn_3796_;
v_x_3788_ = v___x_3798_;
v_x_3789_ = v___x_3800_;
goto _start;
}
else
{
lean_object* v___x_3802_; 
lean_dec(v_x_3789_);
lean_inc_ref(v_post_3786_);
lean_inc_ref(v_pre_3785_);
v___x_3802_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3785_, v_post_3786_, v_x_3787_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; size_t v_sz_3804_; size_t v___x_3805_; lean_object* v___x_3806_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
v_sz_3804_ = lean_array_size(v_x_3788_);
v___x_3805_ = ((size_t)0ULL);
lean_inc_ref(v_post_3786_);
lean_inc_ref(v_pre_3785_);
v___x_3806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_3785_, v_post_3786_, v_sz_3804_, v___x_3805_, v_x_3788_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___x_3808_ = l_Lean_mkAppN(v_a_3803_, v_a_3807_);
lean_dec(v_a_3807_);
v___x_3809_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3785_, v_post_3786_, v___x_3808_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
return v___x_3809_;
}
else
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v_a_3803_);
lean_dec_ref(v_post_3786_);
lean_dec_ref(v_pre_3785_);
v_a_3810_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3812_ = v___x_3806_;
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3806_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3817_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3815_; 
if (v_isShared_3813_ == 0)
{
v___x_3815_ = v___x_3812_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v_a_3810_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_dec_ref(v_x_3788_);
lean_dec_ref(v_post_3786_);
lean_dec_ref(v_pre_3785_);
return v___x_3802_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v___x_3818_, lean_object* v_pre_3819_, lean_object* v_e_3820_, lean_object* v_post_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_Core_checkSystem(v___x_3818_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3829_; 
lean_dec_ref_known(v___x_3828_, 1);
lean_inc_ref(v_pre_3819_);
lean_inc(v___y_3826_);
lean_inc_ref(v___y_3825_);
lean_inc(v___y_3824_);
lean_inc_ref(v___y_3823_);
lean_inc_ref(v_e_3820_);
v___x_3829_ = lean_apply_6(v_pre_3819_, v_e_3820_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, lean_box(0));
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3945_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3832_ = v___x_3829_;
v_isShared_3833_ = v_isSharedCheck_3945_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3829_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3945_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___y_3835_; 
switch(lean_obj_tag(v_a_3830_))
{
case 0:
{
lean_object* v_e_3935_; lean_object* v___x_3937_; 
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_e_3820_);
lean_dec_ref(v_pre_3819_);
v_e_3935_ = lean_ctor_get(v_a_3830_, 0);
lean_inc_ref(v_e_3935_);
lean_dec_ref_known(v_a_3830_, 1);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v_e_3935_);
v___x_3937_ = v___x_3832_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_e_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
case 1:
{
lean_object* v_e_3939_; lean_object* v___x_3940_; 
lean_del_object(v___x_3832_);
lean_dec_ref(v_e_3820_);
v_e_3939_ = lean_ctor_get(v_a_3830_, 0);
lean_inc_ref(v_e_3939_);
lean_dec_ref_known(v_a_3830_, 1);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3940_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_e_3939_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v___x_3942_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3940_, 1);
v___x_3942_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v_a_3941_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3942_;
}
else
{
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3940_;
}
}
default: 
{
lean_object* v_e_x3f_3943_; 
lean_del_object(v___x_3832_);
v_e_x3f_3943_ = lean_ctor_get(v_a_3830_, 0);
lean_inc(v_e_x3f_3943_);
lean_dec_ref_known(v_a_3830_, 1);
if (lean_obj_tag(v_e_x3f_3943_) == 0)
{
v___y_3835_ = v_e_3820_;
goto v___jp_3834_;
}
else
{
lean_object* v_val_3944_; 
lean_dec_ref(v_e_3820_);
v_val_3944_ = lean_ctor_get(v_e_x3f_3943_, 0);
lean_inc(v_val_3944_);
lean_dec_ref_known(v_e_x3f_3943_, 1);
v___y_3835_ = v_val_3944_;
goto v___jp_3834_;
}
}
}
v___jp_3834_:
{
switch(lean_obj_tag(v___y_3835_))
{
case 7:
{
lean_object* v_binderName_3836_; lean_object* v_binderType_3837_; lean_object* v_body_3838_; uint8_t v_binderInfo_3839_; lean_object* v___x_3840_; 
v_binderName_3836_ = lean_ctor_get(v___y_3835_, 0);
v_binderType_3837_ = lean_ctor_get(v___y_3835_, 1);
v_body_3838_ = lean_ctor_get(v___y_3835_, 2);
v_binderInfo_3839_ = lean_ctor_get_uint8(v___y_3835_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3837_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3840_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_binderType_3837_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
lean_inc_ref(v_body_3838_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3842_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_body_3838_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; size_t v___x_3844_; size_t v___x_3845_; uint8_t v___x_3846_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref_known(v___x_3842_, 1);
v___x_3844_ = lean_ptr_addr(v_binderType_3837_);
v___x_3845_ = lean_ptr_addr(v_a_3841_);
v___x_3846_ = lean_usize_dec_eq(v___x_3844_, v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_inc(v_binderName_3836_);
lean_dec_ref_known(v___y_3835_, 3);
v___x_3847_ = l_Lean_Expr_forallE___override(v_binderName_3836_, v_a_3841_, v_a_3843_, v_binderInfo_3839_);
v___x_3848_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3847_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3848_;
}
else
{
size_t v___x_3849_; size_t v___x_3850_; uint8_t v___x_3851_; 
v___x_3849_ = lean_ptr_addr(v_body_3838_);
v___x_3850_ = lean_ptr_addr(v_a_3843_);
v___x_3851_ = lean_usize_dec_eq(v___x_3849_, v___x_3850_);
if (v___x_3851_ == 0)
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
lean_inc(v_binderName_3836_);
lean_dec_ref_known(v___y_3835_, 3);
v___x_3852_ = l_Lean_Expr_forallE___override(v_binderName_3836_, v_a_3841_, v_a_3843_, v_binderInfo_3839_);
v___x_3853_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3852_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3853_;
}
else
{
uint8_t v___x_3854_; 
v___x_3854_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3839_, v_binderInfo_3839_);
if (v___x_3854_ == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
lean_inc(v_binderName_3836_);
lean_dec_ref_known(v___y_3835_, 3);
v___x_3855_ = l_Lean_Expr_forallE___override(v_binderName_3836_, v_a_3841_, v_a_3843_, v_binderInfo_3839_);
v___x_3856_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3855_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3856_;
}
else
{
lean_object* v___x_3857_; 
lean_dec(v_a_3843_);
lean_dec(v_a_3841_);
v___x_3857_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___y_3835_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3857_;
}
}
}
}
else
{
lean_dec(v_a_3841_);
lean_dec_ref_known(v___y_3835_, 3);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3842_;
}
}
else
{
lean_dec_ref_known(v___y_3835_, 3);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3840_;
}
}
case 6:
{
lean_object* v_binderName_3858_; lean_object* v_binderType_3859_; lean_object* v_body_3860_; uint8_t v_binderInfo_3861_; lean_object* v___x_3862_; 
v_binderName_3858_ = lean_ctor_get(v___y_3835_, 0);
v_binderType_3859_ = lean_ctor_get(v___y_3835_, 1);
v_body_3860_ = lean_ctor_get(v___y_3835_, 2);
v_binderInfo_3861_ = lean_ctor_get_uint8(v___y_3835_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3859_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3862_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_binderType_3859_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3864_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
lean_inc_ref(v_body_3860_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3864_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_body_3860_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; size_t v___x_3866_; size_t v___x_3867_; uint8_t v___x_3868_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___x_3866_ = lean_ptr_addr(v_binderType_3859_);
v___x_3867_ = lean_ptr_addr(v_a_3863_);
v___x_3868_ = lean_usize_dec_eq(v___x_3866_, v___x_3867_);
if (v___x_3868_ == 0)
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
lean_inc(v_binderName_3858_);
lean_dec_ref_known(v___y_3835_, 3);
v___x_3869_ = l_Lean_Expr_lam___override(v_binderName_3858_, v_a_3863_, v_a_3865_, v_binderInfo_3861_);
v___x_3870_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3869_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3870_;
}
else
{
size_t v___x_3871_; size_t v___x_3872_; uint8_t v___x_3873_; 
v___x_3871_ = lean_ptr_addr(v_body_3860_);
v___x_3872_ = lean_ptr_addr(v_a_3865_);
v___x_3873_ = lean_usize_dec_eq(v___x_3871_, v___x_3872_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_inc(v_binderName_3858_);
lean_dec_ref_known(v___y_3835_, 3);
v___x_3874_ = l_Lean_Expr_lam___override(v_binderName_3858_, v_a_3863_, v_a_3865_, v_binderInfo_3861_);
v___x_3875_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3874_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3875_;
}
else
{
uint8_t v___x_3876_; 
v___x_3876_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_3861_, v_binderInfo_3861_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
lean_inc(v_binderName_3858_);
lean_dec_ref_known(v___y_3835_, 3);
v___x_3877_ = l_Lean_Expr_lam___override(v_binderName_3858_, v_a_3863_, v_a_3865_, v_binderInfo_3861_);
v___x_3878_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3877_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; 
lean_dec(v_a_3865_);
lean_dec(v_a_3863_);
v___x_3879_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___y_3835_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3879_;
}
}
}
}
else
{
lean_dec(v_a_3863_);
lean_dec_ref_known(v___y_3835_, 3);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3864_;
}
}
else
{
lean_dec_ref_known(v___y_3835_, 3);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3862_;
}
}
case 8:
{
lean_object* v_declName_3880_; lean_object* v_type_3881_; lean_object* v_value_3882_; lean_object* v_body_3883_; uint8_t v_nondep_3884_; lean_object* v___x_3885_; 
v_declName_3880_ = lean_ctor_get(v___y_3835_, 0);
v_type_3881_ = lean_ctor_get(v___y_3835_, 1);
v_value_3882_ = lean_ctor_get(v___y_3835_, 2);
v_body_3883_ = lean_ctor_get(v___y_3835_, 3);
v_nondep_3884_ = lean_ctor_get_uint8(v___y_3835_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3881_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3885_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_type_3881_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
lean_inc_ref(v_value_3882_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3887_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_value_3882_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3889_; 
v_a_3888_ = lean_ctor_get(v___x_3887_, 0);
lean_inc(v_a_3888_);
lean_dec_ref_known(v___x_3887_, 1);
lean_inc_ref(v_body_3883_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3889_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_body_3883_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3889_) == 0)
{
lean_object* v_a_3890_; size_t v___x_3891_; size_t v___x_3892_; uint8_t v___x_3893_; 
v_a_3890_ = lean_ctor_get(v___x_3889_, 0);
lean_inc(v_a_3890_);
lean_dec_ref_known(v___x_3889_, 1);
v___x_3891_ = lean_ptr_addr(v_type_3881_);
v___x_3892_ = lean_ptr_addr(v_a_3886_);
v___x_3893_ = lean_usize_dec_eq(v___x_3891_, v___x_3892_);
if (v___x_3893_ == 0)
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_inc(v_declName_3880_);
lean_dec_ref_known(v___y_3835_, 4);
v___x_3894_ = l_Lean_Expr_letE___override(v_declName_3880_, v_a_3886_, v_a_3888_, v_a_3890_, v_nondep_3884_);
v___x_3895_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3894_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3895_;
}
else
{
size_t v___x_3896_; size_t v___x_3897_; uint8_t v___x_3898_; 
v___x_3896_ = lean_ptr_addr(v_value_3882_);
v___x_3897_ = lean_ptr_addr(v_a_3888_);
v___x_3898_ = lean_usize_dec_eq(v___x_3896_, v___x_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
lean_inc(v_declName_3880_);
lean_dec_ref_known(v___y_3835_, 4);
v___x_3899_ = l_Lean_Expr_letE___override(v_declName_3880_, v_a_3886_, v_a_3888_, v_a_3890_, v_nondep_3884_);
v___x_3900_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3899_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3900_;
}
else
{
size_t v___x_3901_; size_t v___x_3902_; uint8_t v___x_3903_; 
v___x_3901_ = lean_ptr_addr(v_body_3883_);
v___x_3902_ = lean_ptr_addr(v_a_3890_);
v___x_3903_ = lean_usize_dec_eq(v___x_3901_, v___x_3902_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_inc(v_declName_3880_);
lean_dec_ref_known(v___y_3835_, 4);
v___x_3904_ = l_Lean_Expr_letE___override(v_declName_3880_, v_a_3886_, v_a_3888_, v_a_3890_, v_nondep_3884_);
v___x_3905_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3904_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3905_;
}
else
{
lean_object* v___x_3906_; 
lean_dec(v_a_3890_);
lean_dec(v_a_3888_);
lean_dec(v_a_3886_);
v___x_3906_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___y_3835_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3906_;
}
}
}
}
else
{
lean_dec(v_a_3888_);
lean_dec(v_a_3886_);
lean_dec_ref_known(v___y_3835_, 4);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3889_;
}
}
else
{
lean_dec(v_a_3886_);
lean_dec_ref_known(v___y_3835_, 4);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3887_;
}
}
else
{
lean_dec_ref_known(v___y_3835_, 4);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3885_;
}
}
case 5:
{
lean_object* v_dummy_3907_; lean_object* v_nargs_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_dummy_3907_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3908_ = l_Lean_Expr_getAppNumArgs(v___y_3835_);
lean_inc(v_nargs_3908_);
v___x_3909_ = lean_mk_array(v_nargs_3908_, v_dummy_3907_);
v___x_3910_ = lean_unsigned_to_nat(1u);
v___x_3911_ = lean_nat_sub(v_nargs_3908_, v___x_3910_);
lean_dec(v_nargs_3908_);
v___x_3912_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3819_, v_post_3821_, v___y_3835_, v___x_3909_, v___x_3911_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3912_;
}
case 10:
{
lean_object* v_data_3913_; lean_object* v_expr_3914_; lean_object* v___x_3915_; 
v_data_3913_ = lean_ctor_get(v___y_3835_, 0);
v_expr_3914_ = lean_ctor_get(v___y_3835_, 1);
lean_inc_ref(v_expr_3914_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3915_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_expr_3914_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; size_t v___x_3917_; size_t v___x_3918_; uint8_t v___x_3919_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = lean_ptr_addr(v_expr_3914_);
v___x_3918_ = lean_ptr_addr(v_a_3916_);
v___x_3919_ = lean_usize_dec_eq(v___x_3917_, v___x_3918_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
lean_inc(v_data_3913_);
lean_dec_ref_known(v___y_3835_, 2);
v___x_3920_ = l_Lean_Expr_mdata___override(v_data_3913_, v_a_3916_);
v___x_3921_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3920_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3921_;
}
else
{
lean_object* v___x_3922_; 
lean_dec(v_a_3916_);
v___x_3922_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___y_3835_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3922_;
}
}
else
{
lean_dec_ref_known(v___y_3835_, 2);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3915_;
}
}
case 11:
{
lean_object* v_typeName_3923_; lean_object* v_idx_3924_; lean_object* v_struct_3925_; lean_object* v___x_3926_; 
v_typeName_3923_ = lean_ctor_get(v___y_3835_, 0);
v_idx_3924_ = lean_ctor_get(v___y_3835_, 1);
v_struct_3925_ = lean_ctor_get(v___y_3835_, 2);
lean_inc_ref(v_struct_3925_);
lean_inc_ref(v_post_3821_);
lean_inc_ref(v_pre_3819_);
v___x_3926_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3819_, v_post_3821_, v_struct_3925_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; size_t v___x_3928_; size_t v___x_3929_; uint8_t v___x_3930_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v___x_3926_, 1);
v___x_3928_ = lean_ptr_addr(v_struct_3925_);
v___x_3929_ = lean_ptr_addr(v_a_3927_);
v___x_3930_ = lean_usize_dec_eq(v___x_3928_, v___x_3929_);
if (v___x_3930_ == 0)
{
lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_inc(v_idx_3924_);
lean_inc(v_typeName_3923_);
lean_dec_ref_known(v___y_3835_, 3);
v___x_3931_ = l_Lean_Expr_proj___override(v_typeName_3923_, v_idx_3924_, v_a_3927_);
v___x_3932_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___x_3931_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3932_;
}
else
{
lean_object* v___x_3933_; 
lean_dec(v_a_3927_);
v___x_3933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___y_3835_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3933_;
}
}
else
{
lean_dec_ref_known(v___y_3835_, 3);
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_pre_3819_);
return v___x_3926_;
}
}
default: 
{
lean_object* v___x_3934_; 
v___x_3934_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3819_, v_post_3821_, v___y_3835_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
return v___x_3934_;
}
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_e_3820_);
lean_dec_ref(v_pre_3819_);
v_a_3946_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3829_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3829_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v_post_3821_);
lean_dec_ref(v_e_3820_);
lean_dec_ref(v_pre_3819_);
v_a_3954_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3828_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3828_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v___x_3962_, lean_object* v_pre_3963_, lean_object* v_e_3964_, lean_object* v_post_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v___x_3962_, v_pre_3963_, v_e_3964_, v_post_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec(v___y_3966_);
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_3973_, lean_object* v_post_3974_, lean_object* v_e_3975_, lean_object* v_a_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
lean_inc(v_a_3976_);
v___x_3982_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3982_, 0, lean_box(0));
lean_closure_set(v___x_3982_, 1, lean_box(0));
lean_closure_set(v___x_3982_, 2, v_a_3976_);
v___x_3983_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3982_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_3983_) == 0)
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4015_; 
v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_3986_ = v___x_3983_;
v_isShared_3987_ = v_isSharedCheck_4015_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4015_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3984_, v_e_3975_);
lean_dec(v_a_3984_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3989_; lean_object* v___f_3990_; lean_object* v___x_3991_; 
lean_del_object(v___x_3986_);
v___x_3989_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
lean_inc_ref(v_e_3975_);
v___f_3990_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3990_, 0, v___x_3989_);
lean_closure_set(v___f_3990_, 1, v_pre_3973_);
lean_closure_set(v___f_3990_, 2, v_e_3975_);
lean_closure_set(v___f_3990_, 3, v_post_3974_);
v___x_3991_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v___f_3990_, v_a_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___f_3993_; lean_object* v___x_3994_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc_n(v_a_3992_, 2);
lean_dec_ref_known(v___x_3991_, 1);
lean_inc(v_a_3976_);
v___f_3993_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3993_, 0, v_a_3976_);
lean_closure_set(v___f_3993_, 1, v_e_3975_);
lean_closure_set(v___f_3993_, 2, v_a_3992_);
v___x_3994_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3993_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4001_ == 0)
{
lean_object* v_unused_4002_; 
v_unused_4002_ = lean_ctor_get(v___x_3994_, 0);
lean_dec(v_unused_4002_);
v___x_3996_ = v___x_3994_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_dec(v___x_3994_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
lean_ctor_set(v___x_3996_, 0, v_a_3992_);
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3992_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec(v_a_3992_);
v_a_4003_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3994_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3994_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
else
{
lean_dec_ref(v_e_3975_);
return v___x_3991_;
}
}
else
{
lean_object* v_val_4011_; lean_object* v___x_4013_; 
lean_dec_ref(v_e_3975_);
lean_dec_ref(v_post_3974_);
lean_dec_ref(v_pre_3973_);
v_val_4011_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_val_4011_);
lean_dec_ref_known(v___x_3988_, 1);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v_val_4011_);
v___x_4013_ = v___x_3986_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_val_4011_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v_e_3975_);
lean_dec_ref(v_post_3974_);
lean_dec_ref(v_pre_3973_);
v_a_4016_ = lean_ctor_get(v___x_3983_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3983_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3983_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_4024_, lean_object* v_post_4025_, lean_object* v_e_4026_, lean_object* v_a_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
lean_inc_ref(v_post_4025_);
lean_inc(v___y_4031_);
lean_inc_ref(v___y_4030_);
lean_inc(v___y_4029_);
lean_inc_ref(v___y_4028_);
lean_inc_ref(v_e_4026_);
v___x_4033_ = lean_apply_6(v_post_4025_, v_e_4026_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, lean_box(0));
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4052_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4052_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4052_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
switch(lean_obj_tag(v_a_4034_))
{
case 0:
{
lean_object* v_e_4038_; lean_object* v___x_4040_; 
lean_dec_ref(v_e_4026_);
lean_dec_ref(v_post_4025_);
lean_dec_ref(v_pre_4024_);
v_e_4038_ = lean_ctor_get(v_a_4034_, 0);
lean_inc_ref(v_e_4038_);
lean_dec_ref_known(v_a_4034_, 1);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v_e_4038_);
v___x_4040_ = v___x_4036_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_e_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
case 1:
{
lean_object* v_e_4042_; lean_object* v___x_4043_; 
lean_del_object(v___x_4036_);
lean_dec_ref(v_e_4026_);
v_e_4042_ = lean_ctor_get(v_a_4034_, 0);
lean_inc_ref(v_e_4042_);
lean_dec_ref_known(v_a_4034_, 1);
v___x_4043_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4024_, v_post_4025_, v_e_4042_, v_a_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4043_;
}
default: 
{
lean_object* v_e_x3f_4044_; 
lean_dec_ref(v_post_4025_);
lean_dec_ref(v_pre_4024_);
v_e_x3f_4044_ = lean_ctor_get(v_a_4034_, 0);
lean_inc(v_e_x3f_4044_);
lean_dec_ref_known(v_a_4034_, 1);
if (lean_obj_tag(v_e_x3f_4044_) == 0)
{
lean_object* v___x_4046_; 
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v_e_4026_);
v___x_4046_ = v___x_4036_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_e_4026_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
else
{
lean_object* v_val_4048_; lean_object* v___x_4050_; 
lean_dec_ref(v_e_4026_);
v_val_4048_ = lean_ctor_get(v_e_x3f_4044_, 0);
lean_inc(v_val_4048_);
lean_dec_ref_known(v_e_x3f_4044_, 1);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v_val_4048_);
v___x_4050_ = v___x_4036_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_val_4048_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v_e_4026_);
lean_dec_ref(v_post_4025_);
lean_dec_ref(v_pre_4024_);
v_a_4053_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4033_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4033_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4061_, lean_object* v_post_4062_, lean_object* v_e_4063_, lean_object* v_a_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4061_, v_post_4062_, v_e_4063_, v_a_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v_a_4064_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6___boxed(lean_object* v_pre_4071_, lean_object* v_post_4072_, lean_object* v_sz_4073_, lean_object* v_i_4074_, lean_object* v_bs_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
size_t v_sz_boxed_4082_; size_t v_i_boxed_4083_; lean_object* v_res_4084_; 
v_sz_boxed_4082_ = lean_unbox_usize(v_sz_4073_);
lean_dec(v_sz_4073_);
v_i_boxed_4083_ = lean_unbox_usize(v_i_4074_);
lean_dec(v_i_4074_);
v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_4071_, v_post_4072_, v_sz_boxed_4082_, v_i_boxed_4083_, v_bs_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4085_, lean_object* v_post_4086_, lean_object* v_x_4087_, lean_object* v_x_4088_, lean_object* v_x_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4085_, v_post_4086_, v_x_4087_, v_x_4088_, v_x_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object* v_pre_4097_, lean_object* v_post_4098_, lean_object* v_e_4099_, lean_object* v_a_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4097_, v_post_4098_, v_e_4099_, v_a_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v_a_4100_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object* v_input_4107_, lean_object* v_pre_4108_, lean_object* v_post_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v_a_4117_; lean_object* v___x_4118_; 
v___x_4115_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_4116_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4115_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4108_, v_post_4109_, v_input_4107_, v_a_4117_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4128_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v___x_4120_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4120_, 0, lean_box(0));
lean_closure_set(v___x_4120_, 1, lean_box(0));
lean_closure_set(v___x_4120_, 2, v_a_4117_);
v___x_4121_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4120_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4121_);
if (v_isSharedCheck_4128_ == 0)
{
lean_object* v_unused_4129_; 
v_unused_4129_ = lean_ctor_get(v___x_4121_, 0);
lean_dec(v_unused_4129_);
v___x_4123_ = v___x_4121_;
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
else
{
lean_dec(v___x_4121_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4128_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
lean_object* v___x_4126_; 
if (v_isShared_4124_ == 0)
{
lean_ctor_set(v___x_4123_, 0, v_a_4119_);
v___x_4126_ = v___x_4123_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_a_4119_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
else
{
lean_dec(v_a_4117_);
return v___x_4118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object* v_input_4130_, lean_object* v_pre_4131_, lean_object* v_post_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4130_, v_pre_4131_, v_post_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
return v_res_4138_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4139_; double v___x_4140_; 
v___x_4139_ = lean_unsigned_to_nat(0u);
v___x_4140_ = lean_float_of_nat(v___x_4139_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_4144_, lean_object* v_msg_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v_ref_4151_; lean_object* v___x_4152_; lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4198_; 
v_ref_4151_ = lean_ctor_get(v___y_4148_, 2);
v___x_4152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4198_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4198_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4157_; lean_object* v_traceState_4158_; lean_object* v_env_4159_; lean_object* v_nextMacroScope_4160_; lean_object* v_ngen_4161_; lean_object* v_auxDeclNGen_4162_; lean_object* v_cache_4163_; lean_object* v_recordedDeps_4164_; lean_object* v_messages_4165_; lean_object* v_infoState_4166_; lean_object* v_snapshotTasks_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4197_; 
v___x_4157_ = lean_st_ref_take(v___y_4149_);
v_traceState_4158_ = lean_ctor_get(v___x_4157_, 4);
v_env_4159_ = lean_ctor_get(v___x_4157_, 0);
v_nextMacroScope_4160_ = lean_ctor_get(v___x_4157_, 1);
v_ngen_4161_ = lean_ctor_get(v___x_4157_, 2);
v_auxDeclNGen_4162_ = lean_ctor_get(v___x_4157_, 3);
v_cache_4163_ = lean_ctor_get(v___x_4157_, 5);
v_recordedDeps_4164_ = lean_ctor_get(v___x_4157_, 6);
v_messages_4165_ = lean_ctor_get(v___x_4157_, 7);
v_infoState_4166_ = lean_ctor_get(v___x_4157_, 8);
v_snapshotTasks_4167_ = lean_ctor_get(v___x_4157_, 9);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4169_ = v___x_4157_;
v_isShared_4170_ = v_isSharedCheck_4197_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_snapshotTasks_4167_);
lean_inc(v_infoState_4166_);
lean_inc(v_messages_4165_);
lean_inc(v_recordedDeps_4164_);
lean_inc(v_cache_4163_);
lean_inc(v_traceState_4158_);
lean_inc(v_auxDeclNGen_4162_);
lean_inc(v_ngen_4161_);
lean_inc(v_nextMacroScope_4160_);
lean_inc(v_env_4159_);
lean_dec(v___x_4157_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4197_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
uint64_t v_tid_4171_; lean_object* v_traces_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4196_; 
v_tid_4171_ = lean_ctor_get_uint64(v_traceState_4158_, sizeof(void*)*1);
v_traces_4172_ = lean_ctor_get(v_traceState_4158_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v_traceState_4158_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4174_ = v_traceState_4158_;
v_isShared_4175_ = v_isSharedCheck_4196_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_traces_4172_);
lean_dec(v_traceState_4158_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4196_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; double v___x_4178_; uint8_t v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4187_; 
v___x_4176_ = lean_box(0);
v___x_4177_ = lean_box(0);
v___x_4178_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0);
v___x_4179_ = 0;
v___x_4180_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1));
v___x_4181_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4181_, 0, v_cls_4144_);
lean_ctor_set(v___x_4181_, 1, v___x_4177_);
lean_ctor_set(v___x_4181_, 2, v___x_4180_);
lean_ctor_set_float(v___x_4181_, sizeof(void*)*3, v___x_4178_);
lean_ctor_set_float(v___x_4181_, sizeof(void*)*3 + 8, v___x_4178_);
lean_ctor_set_uint8(v___x_4181_, sizeof(void*)*3 + 16, v___x_4179_);
v___x_4182_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2));
v___x_4183_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4181_);
lean_ctor_set(v___x_4183_, 1, v_a_4153_);
lean_ctor_set(v___x_4183_, 2, v___x_4182_);
lean_inc(v_ref_4151_);
v___x_4184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4184_, 0, v_ref_4151_);
lean_ctor_set(v___x_4184_, 1, v___x_4183_);
v___x_4185_ = l_Lean_PersistentArray_push___redArg(v_traces_4172_, v___x_4184_);
if (v_isShared_4175_ == 0)
{
lean_ctor_set(v___x_4174_, 0, v___x_4185_);
v___x_4187_ = v___x_4174_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4195_; 
v_reuseFailAlloc_4195_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4185_);
lean_ctor_set_uint64(v_reuseFailAlloc_4195_, sizeof(void*)*1, v_tid_4171_);
v___x_4187_ = v_reuseFailAlloc_4195_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
lean_object* v___x_4189_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 4, v___x_4187_);
v___x_4189_ = v___x_4169_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_env_4159_);
lean_ctor_set(v_reuseFailAlloc_4194_, 1, v_nextMacroScope_4160_);
lean_ctor_set(v_reuseFailAlloc_4194_, 2, v_ngen_4161_);
lean_ctor_set(v_reuseFailAlloc_4194_, 3, v_auxDeclNGen_4162_);
lean_ctor_set(v_reuseFailAlloc_4194_, 4, v___x_4187_);
lean_ctor_set(v_reuseFailAlloc_4194_, 5, v_cache_4163_);
lean_ctor_set(v_reuseFailAlloc_4194_, 6, v_recordedDeps_4164_);
lean_ctor_set(v_reuseFailAlloc_4194_, 7, v_messages_4165_);
lean_ctor_set(v_reuseFailAlloc_4194_, 8, v_infoState_4166_);
lean_ctor_set(v_reuseFailAlloc_4194_, 9, v_snapshotTasks_4167_);
v___x_4189_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
lean_object* v___x_4190_; lean_object* v___x_4192_; 
v___x_4190_ = lean_st_ref_put(v___y_4149_, v___x_4189_);
if (v_isShared_4156_ == 0)
{
lean_ctor_set(v___x_4155_, 0, v___x_4176_);
v___x_4192_ = v___x_4155_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v___x_4176_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_4199_, lean_object* v_msg_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_4199_, v_msg_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4207_, size_t v_i_4208_, lean_object* v_bs_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_){
_start:
{
uint8_t v___x_4215_; 
v___x_4215_ = lean_usize_dec_lt(v_i_4208_, v_sz_4207_);
if (v___x_4215_ == 0)
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v_bs_4209_);
return v___x_4216_;
}
else
{
lean_object* v_v_4217_; lean_object* v___x_4218_; lean_object* v_bs_x27_4219_; lean_object* v___x_4220_; 
v_v_4217_ = lean_array_uget(v_bs_4209_, v_i_4208_);
v___x_4218_ = lean_unsigned_to_nat(0u);
v_bs_x27_4219_ = lean_array_uset(v_bs_4209_, v_i_4208_, v___x_4218_);
v___x_4220_ = l_Lean_Elab_WF_mkWfParam(v_v_4217_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; size_t v___x_4222_; size_t v___x_4223_; lean_object* v___x_4224_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
v___x_4222_ = ((size_t)1ULL);
v___x_4223_ = lean_usize_add(v_i_4208_, v___x_4222_);
v___x_4224_ = lean_array_uset(v_bs_x27_4219_, v_i_4208_, v_a_4221_);
v_i_4208_ = v___x_4223_;
v_bs_4209_ = v___x_4224_;
goto _start;
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v_bs_x27_4219_);
v_a_4226_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4220_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4220_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4234_, lean_object* v_i_4235_, lean_object* v_bs_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
size_t v_sz_boxed_4242_; size_t v_i_boxed_4243_; lean_object* v_res_4244_; 
v_sz_boxed_4242_ = lean_unbox_usize(v_sz_4234_);
lean_dec(v_sz_4234_);
v_i_boxed_4243_ = lean_unbox_usize(v_i_4235_);
lean_dec(v_i_4235_);
v_res_4244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4242_, v_i_boxed_4243_, v_bs_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
return v_res_4244_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_4245_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4246_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_4247_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__0, &l_Lean_Elab_WF_preprocess___lam__2___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0);
v___x_4248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
lean_ctor_set(v___x_4248_, 2, v___x_4246_);
lean_ctor_set(v___x_4248_, 3, v___x_4246_);
return v___x_4248_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
return v___x_4250_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3(void){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = lean_unsigned_to_nat(0u);
v___x_4252_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4252_);
lean_ctor_set(v___x_4253_, 1, v___x_4251_);
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = lean_unsigned_to_nat(32u);
v___x_4255_ = lean_mk_empty_array_with_capacity(v___x_4254_);
v___x_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
return v___x_4256_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5(void){
_start:
{
size_t v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4257_ = ((size_t)5ULL);
v___x_4258_ = lean_unsigned_to_nat(0u);
v___x_4259_ = lean_unsigned_to_nat(32u);
v___x_4260_ = lean_mk_empty_array_with_capacity(v___x_4259_);
v___x_4261_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4262_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4262_, 0, v___x_4261_);
lean_ctor_set(v___x_4262_, 1, v___x_4260_);
lean_ctor_set(v___x_4262_, 2, v___x_4258_);
lean_ctor_set(v___x_4262_, 3, v___x_4258_);
lean_ctor_set_usize(v___x_4262_, 4, v___x_4257_);
return v___x_4262_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__5, &l_Lean_Elab_WF_preprocess___lam__2___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5);
v___x_4264_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4265_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
lean_ctor_set(v___x_4265_, 2, v___x_4264_);
lean_ctor_set(v___x_4265_, 3, v___x_4263_);
return v___x_4265_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4266_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__6, &l_Lean_Elab_WF_preprocess___lam__2___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6);
v___x_4267_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__3, &l_Lean_Elab_WF_preprocess___lam__2___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3);
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
lean_ctor_set(v___x_4268_, 1, v___x_4266_);
return v___x_4268_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__12(void){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4277_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__9));
v___x_4278_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4279_ = l_Lean_Name_append(v___x_4278_, v___x_4277_);
return v___x_4279_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14(void){
_start:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__13));
v___x_4282_ = l_Lean_stringToMessageData(v___x_4281_);
return v___x_4282_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16(void){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__15));
v___x_4285_ = l_Lean_stringToMessageData(v___x_4284_);
return v___x_4285_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18(void){
_start:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__17));
v___x_4288_ = l_Lean_stringToMessageData(v___x_4287_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2(lean_object* v_a_4289_, uint8_t v___x_4290_, lean_object* v___f_4291_, lean_object* v___f_4292_, lean_object* v_xs_4293_, lean_object* v_x_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
size_t v_sz_4300_; size_t v___x_4301_; lean_object* v___x_4302_; 
v_sz_4300_ = lean_array_size(v_xs_4293_);
v___x_4301_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4293_);
v___x_4302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4300_, v___x_4301_, v_xs_4293_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = l_Lean_Expr_beta(v_a_4289_, v_a_4303_);
v___x_4305_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__1, &l_Lean_Elab_WF_preprocess___lam__2___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1);
v___x_4306_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__28___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_3392239133____hygCtx___hyg_10_));
v___x_4307_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4305_, v___x_4306_, v___x_4290_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4307_) == 0)
{
lean_object* v_a_4308_; lean_object* v___x_4309_; uint8_t v___x_4310_; lean_object* v___x_4311_; 
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4307_, 1);
v___x_4309_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__33___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2646010003____hygCtx___hyg_10_));
v___x_4310_ = 0;
v___x_4311_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4308_, v___x_4309_, v___x_4310_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
v___x_4313_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__62___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2527999769____hygCtx___hyg_10_));
v___x_4314_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4312_, v___x_4313_, v___x_4290_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4295_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = lean_unsigned_to_nat(1u);
v___x_4319_ = lean_mk_empty_array_with_capacity(v___x_4318_);
v___x_4320_ = lean_array_push(v___x_4319_, v_a_4315_);
v___x_4321_ = lean_box(0);
v___x_4322_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__7, &l_Lean_Elab_WF_preprocess___lam__2___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7);
lean_inc_ref(v___x_4304_);
v___x_4323_ = l_Lean_Meta_simp(v___x_4304_, v_a_4317_, v___x_4320_, v___x_4321_, v___x_4322_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v_fst_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4394_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref_known(v___x_4323_, 1);
v_fst_4325_ = lean_ctor_get(v_a_4324_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_a_4324_);
if (v_isSharedCheck_4394_ == 0)
{
lean_object* v_unused_4395_; 
v_unused_4395_ = lean_ctor_get(v_a_4324_, 1);
lean_dec(v_unused_4395_);
v___x_4327_ = v_a_4324_;
v_isShared_4328_ = v_isSharedCheck_4394_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_fst_4325_);
lean_dec(v_a_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4394_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v_expr_4329_; lean_object* v_proof_x3f_4330_; uint8_t v_cache_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4393_; 
v_expr_4329_ = lean_ctor_get(v_fst_4325_, 0);
v_proof_x3f_4330_ = lean_ctor_get(v_fst_4325_, 1);
v_cache_4331_ = lean_ctor_get_uint8(v_fst_4325_, sizeof(void*)*2);
v_isSharedCheck_4393_ = !lean_is_exclusive(v_fst_4325_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4333_ = v_fst_4325_;
v_isShared_4334_ = v_isSharedCheck_4393_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_proof_x3f_4330_);
lean_inc(v_expr_4329_);
lean_dec(v_fst_4325_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4393_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4335_; 
lean_inc_ref(v_expr_4329_);
v___x_4335_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4329_, v___f_4291_, v___f_4292_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4337_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
v___x_4337_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4336_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v___y_4343_; lean_object* v_toCold_4348_; lean_object* v_options_4349_; uint8_t v_hasTrace_4350_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4338_);
lean_dec_ref_known(v___x_4337_, 1);
v_toCold_4348_ = lean_ctor_get(v___y_4297_, 0);
v_options_4349_ = lean_ctor_get(v_toCold_4348_, 2);
v_hasTrace_4350_ = lean_ctor_get_uint8(v_options_4349_, sizeof(void*)*1);
if (v_hasTrace_4350_ == 0)
{
lean_dec_ref(v_expr_4329_);
lean_del_object(v___x_4327_);
lean_dec_ref(v___x_4304_);
v___y_4340_ = v___y_4295_;
v___y_4341_ = v___y_4296_;
v___y_4342_ = v___y_4297_;
v___y_4343_ = v___y_4298_;
goto v___jp_4339_;
}
else
{
lean_object* v_inheritedTraceOptions_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v_inheritedTraceOptions_4351_ = lean_ctor_get(v_toCold_4348_, 11);
v___x_4352_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__9));
v___x_4353_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__12, &l_Lean_Elab_WF_preprocess___lam__2___closed__12_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__12);
v___x_4354_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4351_, v_options_4349_, v___x_4353_);
if (v___x_4354_ == 0)
{
lean_dec_ref(v_expr_4329_);
lean_del_object(v___x_4327_);
lean_dec_ref(v___x_4304_);
v___y_4340_ = v___y_4295_;
v___y_4341_ = v___y_4296_;
v___y_4342_ = v___y_4297_;
v___y_4343_ = v___y_4298_;
goto v___jp_4339_;
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4358_; 
v___x_4355_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__14, &l_Lean_Elab_WF_preprocess___lam__2___closed__14_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14);
v___x_4356_ = l_Lean_indentExpr(v___x_4304_);
if (v_isShared_4328_ == 0)
{
lean_ctor_set_tag(v___x_4327_, 7);
lean_ctor_set(v___x_4327_, 1, v___x_4356_);
lean_ctor_set(v___x_4327_, 0, v___x_4355_);
v___x_4358_ = v___x_4327_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4376_, 1, v___x_4356_);
v___x_4358_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4359_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__16, &l_Lean_Elab_WF_preprocess___lam__2___closed__16_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16);
v___x_4360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set(v___x_4360_, 1, v___x_4359_);
v___x_4361_ = l_Lean_indentExpr(v_expr_4329_);
v___x_4362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set(v___x_4362_, 1, v___x_4361_);
v___x_4363_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__18, &l_Lean_Elab_WF_preprocess___lam__2___closed__18_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18);
v___x_4364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4362_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
lean_inc(v_a_4338_);
v___x_4365_ = l_Lean_indentExpr(v_a_4338_);
v___x_4366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v___x_4352_, v___x_4366_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_dec_ref_known(v___x_4367_, 1);
v___y_4340_ = v___y_4295_;
v___y_4341_ = v___y_4296_;
v___y_4342_ = v___y_4297_;
v___y_4343_ = v___y_4298_;
goto v___jp_4339_;
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec(v_a_4338_);
lean_del_object(v___x_4333_);
lean_dec(v_proof_x3f_4330_);
lean_dec_ref(v_xs_4293_);
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
}
}
v___jp_4339_:
{
lean_object* v___x_4345_; 
if (v_isShared_4334_ == 0)
{
lean_ctor_set(v___x_4333_, 0, v_a_4338_);
v___x_4345_ = v___x_4333_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v_a_4338_);
lean_ctor_set(v_reuseFailAlloc_4347_, 1, v_proof_x3f_4330_);
lean_ctor_set_uint8(v_reuseFailAlloc_4347_, sizeof(void*)*2, v_cache_4331_);
v___x_4345_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
lean_object* v___x_4346_; 
v___x_4346_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4345_, v_xs_4293_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
lean_dec_ref(v_xs_4293_);
return v___x_4346_;
}
}
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_del_object(v___x_4333_);
lean_dec(v_proof_x3f_4330_);
lean_dec_ref(v_expr_4329_);
lean_del_object(v___x_4327_);
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_xs_4293_);
v_a_4377_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4337_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4337_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_del_object(v___x_4333_);
lean_dec(v_proof_x3f_4330_);
lean_dec_ref(v_expr_4329_);
lean_del_object(v___x_4327_);
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_xs_4293_);
v_a_4385_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4335_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4335_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_xs_4293_);
lean_dec_ref(v___f_4292_);
lean_dec_ref(v___f_4291_);
v_a_4396_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___x_4323_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4323_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec(v_a_4315_);
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_xs_4293_);
lean_dec_ref(v___f_4292_);
lean_dec_ref(v___f_4291_);
v_a_4404_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4316_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4316_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_xs_4293_);
lean_dec_ref(v___f_4292_);
lean_dec_ref(v___f_4291_);
v_a_4412_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4314_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4314_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_xs_4293_);
lean_dec_ref(v___f_4292_);
lean_dec_ref(v___f_4291_);
v_a_4420_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4311_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4311_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
else
{
lean_object* v_a_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4435_; 
lean_dec_ref(v___x_4304_);
lean_dec_ref(v_xs_4293_);
lean_dec_ref(v___f_4292_);
lean_dec_ref(v___f_4291_);
v_a_4428_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4307_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4307_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4433_; 
if (v_isShared_4431_ == 0)
{
v___x_4433_ = v___x_4430_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v_a_4428_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec_ref(v_xs_4293_);
lean_dec_ref(v___f_4292_);
lean_dec_ref(v___f_4291_);
lean_dec_ref(v_a_4289_);
v_a_4436_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4302_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4302_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2___boxed(lean_object* v_a_4444_, lean_object* v___x_4445_, lean_object* v___f_4446_, lean_object* v___f_4447_, lean_object* v_xs_4448_, lean_object* v_x_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
uint8_t v___x_14003__boxed_4455_; lean_object* v_res_4456_; 
v___x_14003__boxed_4455_ = lean_unbox(v___x_4445_);
v_res_4456_ = l_Lean_Elab_WF_preprocess___lam__2(v_a_4444_, v___x_14003__boxed_4455_, v___f_4446_, v___f_4447_, v_xs_4448_, v_x_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec_ref(v_x_4449_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; uint8_t v___x_4466_; uint8_t v___x_4467_; 
v___x_4464_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_4461_);
v___x_4465_ = l_Lean_wf_preprocess;
v___x_4466_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v___x_4464_, v___x_4465_);
lean_dec_ref(v___x_4464_);
v___x_4467_ = 1;
if (v___x_4466_ == 0)
{
lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4468_ = lean_box(0);
v___x_4469_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4469_, 0, v_e_4458_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
lean_ctor_set_uint8(v___x_4469_, sizeof(void*)*2, v___x_4467_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
else
{
lean_object* v___f_4471_; lean_object* v___f_4472_; lean_object* v___x_4473_; 
v___f_4471_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___f_4472_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___x_4473_ = l_Lean_Meta_letToHave(v_e_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4475_; lean_object* v___f_4476_; uint8_t v___x_4477_; lean_object* v___x_4478_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc_n(v_a_4474_, 2);
lean_dec_ref_known(v___x_4473_, 1);
v___x_4475_ = lean_box(v___x_4467_);
v___f_4476_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__2___boxed), 11, 4);
lean_closure_set(v___f_4476_, 0, v_a_4474_);
lean_closure_set(v___f_4476_, 1, v___x_4475_);
lean_closure_set(v___f_4476_, 2, v___f_4471_);
lean_closure_set(v___f_4476_, 3, v___f_4472_);
v___x_4477_ = 0;
v___x_4478_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_a_4474_, v___f_4476_, v___x_4477_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_);
return v___x_4478_;
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
v_a_4479_ = lean_ctor_get(v___x_4473_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4473_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4481_ = v___x_4473_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4473_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_Lean_Elab_WF_preprocess(v_e_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4494_, lean_object* v_x_4495_, lean_object* v_x_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4494_, v_x_4495_, v_x_4496_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4503_, lean_object* v_x_4504_, lean_object* v_x_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4503_, v_x_4504_, v_x_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_4512_, lean_object* v_ref_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
v___x_4517_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_4513_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4518_, lean_object* v_ref_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(v_00_u03b1_4518_, v_ref_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(lean_object* v_00_u03b1_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___redArg();
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12___boxed(lean_object* v_00_u03b1_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_throwInterruptException___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__12(v_00_u03b1_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_00_u03b1_4534_, lean_object* v_x_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_00_u03b1_4543_, lean_object* v_x_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_00_u03b1_4543_, v_x_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
return v_res_4551_;
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
