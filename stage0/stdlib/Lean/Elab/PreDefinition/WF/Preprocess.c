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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
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
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_string_object l_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "preprocess"};
static const lean_object* l_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(215, 131, 155, 94, 122, 149, 97, 118)}};
static const lean_ctor_object l_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 185, 233, 182, 178, 136, 28, 192)}};
static const lean_object* l_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_string_object l_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "pre-process definitions defined by well-founded recursion with the `wf_preprocess` simp set"};
static const lean_object* l_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value)}};
static const lean_object* l_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_wf_preprocess;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "wf_preprocess"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 210, 123, 148, 208, 214, 165, 77)}};
static const lean_object* l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 164, .m_capacity = 164, .m_length = 163, .m_data = "simp lemma used in the preprocessing of well-founded recursive function definitions, in particular to add additional hypotheses to the context. Also see `wfParam`."};
static const lean_object* l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "wfPreprocessSimpExtension"};
static const lean_object* l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_WF_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 145, 22, 80, 3, 32, 9, 26)}};
static const lean_object* l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "paramProj"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(185, 166, 16, 253, 90, 4, 64, 220)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value;
static const lean_array_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12____boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "paramMatcher"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(136, 249, 169, 242, 162, 242, 251, 234)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12____boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14____boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "paramLet"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_0),((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_1),((lean_object*)&l_Lean_Elab_WF_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 25, 43, 203, 194, 237, 195, 214)}};
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value_aux_2),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value),LEAN_SCALAR_PTR_LITERAL(158, 69, 53, 139, 5, 90, 17, 138)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12____boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_WF_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__10_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_WF_preprocess___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_WF_preprocess___lam__2___closed__11_value_aux_1),((lean_object*)&l_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
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
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = ((lean_object*)(l_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_51_ = ((lean_object*)(l_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_));
v___x_52_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4__spec__0(v___x_50_, v___x_51_, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4____boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = ((lean_object*)(l_Lean_Elab_WF_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_70_ = ((lean_object*)(l_Lean_Elab_WF_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_71_ = ((lean_object*)(l_Lean_Elab_WF_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_));
v___x_72_ = l_Lean_Meta_registerSimpAttr(v___x_69_, v___x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2____boxed(lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
return v_res_74_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
v___x_76_ = lean_unsigned_to_nat(16u);
v___x_77_ = lean_mk_array(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__0);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2(void){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_81_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__2);
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; 
v___x_84_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__3);
v___x_85_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__1);
v___x_86_ = 1;
v___x_87_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_84_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*2, v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = l_Lean_Elab_WF_wfPreprocessSimpExtension;
v___x_93_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_92_, v_a_90_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; lean_object* v_maxSteps_96_; lean_object* v_maxDischargeDepth_97_; uint8_t v_contextual_98_; uint8_t v_memoize_99_; uint8_t v_singlePass_100_; uint8_t v_zeta_101_; uint8_t v_beta_102_; uint8_t v_eta_103_; uint8_t v_etaStruct_104_; uint8_t v_iota_105_; uint8_t v_proj_106_; uint8_t v_decide_107_; uint8_t v_arith_108_; uint8_t v_autoUnfold_109_; uint8_t v_failIfUnchanged_110_; uint8_t v_ground_111_; uint8_t v_unfoldPartialApp_112_; uint8_t v_zetaDelta_113_; uint8_t v_index_114_; uint8_t v_implicitDefEqProofs_115_; uint8_t v_zetaUnused_116_; uint8_t v_catchRuntime_117_; uint8_t v_zetaHave_118_; uint8_t v_letToHave_119_; uint8_t v_bitVecOfNat_120_; uint8_t v_warnExponents_121_; uint8_t v_suggestions_122_; lean_object* v_maxSuggestions_123_; uint8_t v_locals_124_; uint8_t v_instances_125_; uint8_t v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref(v___x_93_);
v___x_95_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_96_ = lean_ctor_get(v___x_95_, 0);
v_maxDischargeDepth_97_ = lean_ctor_get(v___x_95_, 1);
v_contextual_98_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3);
v_memoize_99_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 1);
v_singlePass_100_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 2);
v_zeta_101_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 3);
v_beta_102_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 4);
v_eta_103_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 5);
v_etaStruct_104_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 6);
v_iota_105_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 7);
v_proj_106_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 8);
v_decide_107_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 9);
v_arith_108_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 10);
v_autoUnfold_109_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 11);
v_failIfUnchanged_110_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 13);
v_ground_111_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_112_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 15);
v_zetaDelta_113_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 16);
v_index_114_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_115_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 18);
v_zetaUnused_116_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 19);
v_catchRuntime_117_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 20);
v_zetaHave_118_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 21);
v_letToHave_119_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 22);
v_bitVecOfNat_120_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 24);
v_warnExponents_121_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 25);
v_suggestions_122_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 26);
v_maxSuggestions_123_ = lean_ctor_get(v___x_95_, 2);
v_locals_124_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 27);
v_instances_125_ = lean_ctor_get_uint8(v___x_95_, sizeof(void*)*3 + 28);
v___x_126_ = 1;
v___x_127_ = 0;
lean_inc(v_maxSuggestions_123_);
lean_inc(v_maxDischargeDepth_97_);
lean_inc(v_maxSteps_96_);
v___x_128_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_128_, 0, v_maxSteps_96_);
lean_ctor_set(v___x_128_, 1, v_maxDischargeDepth_97_);
lean_ctor_set(v___x_128_, 2, v_maxSuggestions_123_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3, v_contextual_98_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 1, v_memoize_99_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 2, v_singlePass_100_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 3, v_zeta_101_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 4, v_beta_102_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 5, v_eta_103_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 6, v_etaStruct_104_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 7, v_iota_105_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 8, v_proj_106_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 9, v_decide_107_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 10, v_arith_108_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 11, v_autoUnfold_109_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 12, v___x_126_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 13, v_failIfUnchanged_110_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 14, v_ground_111_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 15, v_unfoldPartialApp_112_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 16, v_zetaDelta_113_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 17, v_index_114_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_115_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 19, v_zetaUnused_116_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 20, v_catchRuntime_117_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 21, v_zetaHave_118_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 22, v_letToHave_119_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 23, v___x_127_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 24, v_bitVecOfNat_120_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 25, v_warnExponents_121_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 26, v_suggestions_122_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 27, v_locals_124_);
lean_ctor_set_uint8(v___x_128_, sizeof(void*)*3 + 28, v_instances_125_);
v___x_129_ = lean_unsigned_to_nat(1u);
v___x_130_ = lean_mk_empty_array_with_capacity(v___x_129_);
v___x_131_ = lean_array_push(v___x_130_, v_a_94_);
v___x_132_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___closed__4);
v___x_133_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_128_, v___x_131_, v___x_132_, v_a_88_, v_a_89_, v_a_90_);
return v___x_133_;
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
v_a_134_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_93_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_93_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg___boxed(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v_a_147_, v_a_149_, v_a_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___boxed(lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext(v_a_153_, v_a_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f(lean_object* v_e_162_){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_164_ = lean_unsigned_to_nat(2u);
v___x_165_ = l_Lean_Expr_isAppOfArity(v_e_162_, v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_box(0);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = l_Lean_Expr_appArg_x21(v_e_162_);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_isWfParam_x3f___boxed(lean_object* v_e_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_Elab_WF_isWfParam_x3f(v_e_169_);
lean_dec_ref(v_e_169_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam(lean_object* v_e_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_177_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_mk_empty_array_with_capacity(v___x_178_);
v___x_180_ = lean_array_push(v___x_179_, v_e_171_);
v___x_181_ = l_Lean_Meta_mkAppM(v___x_177_, v___x_180_, v_a_172_, v_a_173_, v_a_174_, v_a_175_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkWfParam___boxed(lean_object* v_e_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Elab_WF_mkWfParam(v_e_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(lean_object* v_declName_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v_env_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_192_ = lean_st_ref_get(v___y_190_);
v_env_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc_ref(v_env_193_);
lean_dec(v___x_192_);
v___x_194_ = l_Lean_Environment_isProjectionFn(v_env_193_, v_declName_189_);
v___x_195_ = lean_box(v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg___boxed(lean_object* v_declName_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_197_, v___y_198_);
lean_dec(v___y_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(lean_object* v_declName_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v_declName_201_, v___y_208_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___boxed(lean_object* v_declName_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0(v_declName_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
lean_dec(v___y_212_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj(lean_object* v_e_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Lean_Expr_isApp(v_e_223_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec_ref(v_e_223_);
v___x_233_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v_fn_235_; lean_object* v_arg_236_; lean_object* v___x_237_; 
v_fn_235_ = lean_ctor_get(v_e_223_, 0);
lean_inc_ref(v_fn_235_);
v_arg_236_ = lean_ctor_get(v_e_223_, 1);
v___x_237_ = l_Lean_Elab_WF_isWfParam_x3f(v_arg_236_);
if (lean_obj_tag(v___x_237_) == 1)
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_281_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_281_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_281_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_281_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_f_242_; uint8_t v___x_243_; 
v_f_242_ = l_Lean_Expr_getAppFn(v_e_223_);
lean_dec_ref(v_e_223_);
v___x_243_ = l_Lean_Expr_isConst(v_f_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec_ref(v_f_242_);
lean_dec(v_val_238_);
lean_dec_ref(v_fn_235_);
v___x_244_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 0);
lean_ctor_set(v___x_240_, 0, v___x_244_);
v___x_246_ = v___x_240_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_280_; 
v___x_248_ = l_Lean_Expr_constName_x21(v_f_242_);
lean_dec_ref(v_f_242_);
v___x_249_ = l_Lean_isProjectionFn___at___00Lean_Elab_WF_paramProj_spec__0___redArg(v___x_248_, v_a_230_);
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_280_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_280_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_280_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
uint8_t v___x_254_; 
v___x_254_ = lean_unbox(v_a_250_);
lean_dec(v_a_250_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_del_object(v___x_240_);
lean_dec(v_val_238_);
lean_dec_ref(v_fn_235_);
v___x_255_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_255_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_del_object(v___x_252_);
v___x_259_ = l_Lean_Expr_app___override(v_fn_235_, v_val_238_);
v___x_260_ = l_Lean_Elab_WF_mkWfParam(v___x_259_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_271_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_271_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_271_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_271_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 0);
lean_ctor_set(v___x_240_, 0, v_a_261_);
v___x_266_ = v___x_240_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_270_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_268_; 
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_266_);
v___x_268_ = v___x_263_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_del_object(v___x_240_);
v_a_272_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_260_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_260_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
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
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_dec(v___x_237_);
lean_dec_ref(v_fn_235_);
lean_dec_ref(v_e_223_);
v___x_282_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___boxed(lean_object* v_e_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_Elab_WF_paramProj(v_e_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_306_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_307_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_308_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_305_, v___x_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12____boxed(lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_();
return v_res_310_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramProj___boxed), 9, 0);
v___x_312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_315_ = 1;
v___x_316_ = lean_obj_once(&l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_);
v___x_317_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_314_, v___x_315_, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14____boxed(lean_object* v_a_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_();
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(lean_object* v_k_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v_b_324_, lean_object* v_c_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc(v___y_329_);
lean_inc_ref(v___y_328_);
lean_inc(v___y_327_);
lean_inc_ref(v___y_326_);
lean_inc(v___y_323_);
lean_inc_ref(v___y_322_);
lean_inc(v___y_321_);
v___x_331_ = lean_apply_10(v_k_320_, v_b_324_, v_c_325_, v___y_321_, v___y_322_, v___y_323_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, lean_box(0));
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed(lean_object* v_k_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v_b_336_, lean_object* v_c_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0(v_k_332_, v___y_333_, v___y_334_, v___y_335_, v_b_336_, v_c_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(lean_object* v_e_344_, lean_object* v_k_345_, uint8_t v_cleanupAnnotations_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___f_355_; uint8_t v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_inc(v___y_349_);
lean_inc_ref(v___y_348_);
lean_inc(v___y_347_);
v___f_355_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_355_, 0, v_k_345_);
lean_closure_set(v___f_355_, 1, v___y_347_);
lean_closure_set(v___f_355_, 2, v___y_348_);
lean_closure_set(v___f_355_, 3, v___y_349_);
v___x_356_ = 1;
v___x_357_ = 0;
v___x_358_ = lean_box(0);
v___x_359_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_344_, v___x_356_, v___x_357_, v___x_356_, v___x_357_, v___x_358_, v___f_355_, v_cleanupAnnotations_346_, v___y_350_, v___y_351_, v___y_352_, v___y_353_);
if (lean_obj_tag(v___x_359_) == 0)
{
return v___x_359_;
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_359_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg___boxed(lean_object* v_e_368_, lean_object* v_k_369_, lean_object* v_cleanupAnnotations_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_379_; lean_object* v_res_380_; 
v_cleanupAnnotations_boxed_379_ = lean_unbox(v_cleanupAnnotations_370_);
v_res_380_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_368_, v_k_369_, v_cleanupAnnotations_boxed_379_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(lean_object* v_00_u03b1_381_, lean_object* v_e_382_, lean_object* v_k_383_, uint8_t v_cleanupAnnotations_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_e_382_, v_k_383_, v_cleanupAnnotations_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___boxed(lean_object* v_00_u03b1_394_, lean_object* v_e_395_, lean_object* v_k_396_, lean_object* v_cleanupAnnotations_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_406_; lean_object* v_res_407_; 
v_cleanupAnnotations_boxed_406_ = lean_unbox(v_cleanupAnnotations_397_);
v_res_407_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1(v_00_u03b1_394_, v_e_395_, v_k_396_, v_cleanupAnnotations_boxed_406_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(size_t v_sz_408_, size_t v_i_409_, lean_object* v_bs_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_lt(v_i_409_, v_sz_408_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v_bs_410_);
return v___x_417_;
}
else
{
lean_object* v_v_418_; lean_object* v___x_419_; 
v_v_418_ = lean_array_uget_borrowed(v_bs_410_, v_i_409_);
lean_inc(v_v_418_);
v___x_419_ = l_Lean_Elab_WF_mkWfParam(v_v_418_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v_bs_x27_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref(v___x_419_);
v___x_421_ = lean_unsigned_to_nat(0u);
v_bs_x27_422_ = lean_array_uset(v_bs_410_, v_i_409_, v___x_421_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_add(v_i_409_, v___x_423_);
v___x_425_ = lean_array_uset(v_bs_x27_422_, v_i_409_, v_a_420_);
v_i_409_ = v___x_424_;
v_bs_410_ = v___x_425_;
goto _start;
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_434_; 
lean_dec_ref(v_bs_410_);
v_a_427_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_434_ == 0)
{
v___x_429_ = v___x_419_;
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_419_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_434_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_432_; 
if (v_isShared_430_ == 0)
{
v___x_432_ = v___x_429_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg___boxed(lean_object* v_sz_435_, lean_object* v_i_436_, lean_object* v_bs_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
size_t v_sz_boxed_443_; size_t v_i_boxed_444_; lean_object* v_res_445_; 
v_sz_boxed_443_ = lean_unbox_usize(v_sz_435_);
lean_dec(v_sz_435_);
v_i_boxed_444_ = lean_unbox_usize(v_i_436_);
lean_dec(v_i_436_);
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_boxed_443_, v_i_boxed_444_, v_bs_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(uint8_t v___x_446_, lean_object* v_xs_447_, lean_object* v_body_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
size_t v_sz_457_; size_t v___x_458_; lean_object* v___x_459_; 
v_sz_457_ = lean_array_size(v_xs_447_);
v___x_458_ = ((size_t)0ULL);
lean_inc_ref(v_xs_447_);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_457_, v___x_458_, v_xs_447_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
if (lean_obj_tag(v___x_459_) == 0)
{
lean_object* v_a_460_; lean_object* v___x_461_; uint8_t v___x_462_; uint8_t v___x_463_; lean_object* v___x_464_; 
v_a_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc(v_a_460_);
lean_dec_ref(v___x_459_);
v___x_461_ = l_Lean_Expr_replaceFVars(v_body_448_, v_xs_447_, v_a_460_);
lean_dec(v_a_460_);
v___x_462_ = 0;
v___x_463_ = 1;
v___x_464_ = l_Lean_Meta_mkLambdaFVars(v_xs_447_, v___x_461_, v___x_462_, v___x_446_, v___x_462_, v___x_446_, v___x_463_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec_ref(v_xs_447_);
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref(v_xs_447_);
v_a_465_ = lean_ctor_get(v___x_459_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_459_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_459_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_459_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0___boxed(lean_object* v___x_473_, lean_object* v_xs_474_, lean_object* v_body_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
uint8_t v___x_21832__boxed_484_; lean_object* v_res_485_; 
v___x_21832__boxed_484_ = lean_unbox(v___x_473_);
v_res_485_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0(v___x_21832__boxed_484_, v_xs_474_, v_body_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v_body_475_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(size_t v_sz_486_, size_t v_i_487_, lean_object* v_bs_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
uint8_t v___x_497_; 
v___x_497_ = lean_usize_dec_lt(v_i_487_, v_sz_486_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v_bs_488_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; lean_object* v___f_500_; lean_object* v_v_501_; uint8_t v___x_502_; lean_object* v___x_503_; 
v___x_499_ = lean_box(v___x_497_);
v___f_500_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___lam__0___boxed), 11, 1);
lean_closure_set(v___f_500_, 0, v___x_499_);
v_v_501_ = lean_array_uget_borrowed(v_bs_488_, v_i_487_);
v___x_502_ = 0;
lean_inc(v_v_501_);
v___x_503_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_paramMatcher_spec__1___redArg(v_v_501_, v___f_500_, v___x_502_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; lean_object* v_bs_x27_506_; size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref(v___x_503_);
v___x_505_ = lean_unsigned_to_nat(0u);
v_bs_x27_506_ = lean_array_uset(v_bs_488_, v_i_487_, v___x_505_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_add(v_i_487_, v___x_507_);
v___x_509_ = lean_array_uset(v_bs_x27_506_, v_i_487_, v_a_504_);
v_i_487_ = v___x_508_;
v_bs_488_ = v___x_509_;
goto _start;
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec_ref(v_bs_488_);
v_a_511_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_503_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_503_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4___boxed(lean_object* v_sz_519_, lean_object* v_i_520_, lean_object* v_bs_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
size_t v_sz_boxed_530_; size_t v_i_boxed_531_; lean_object* v_res_532_; 
v_sz_boxed_530_ = lean_unbox_usize(v_sz_519_);
lean_dec(v_sz_519_);
v_i_boxed_531_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_boxed_530_, v_i_boxed_531_, v_bs_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(lean_object* v_msgData_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v___x_539_; lean_object* v_env_540_; lean_object* v___x_541_; lean_object* v_mctx_542_; lean_object* v_lctx_543_; lean_object* v_options_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_539_ = lean_st_ref_get(v___y_537_);
v_env_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc_ref(v_env_540_);
lean_dec(v___x_539_);
v___x_541_ = lean_st_ref_get(v___y_535_);
v_mctx_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc_ref(v_mctx_542_);
lean_dec(v___x_541_);
v_lctx_543_ = lean_ctor_get(v___y_534_, 2);
v_options_544_ = lean_ctor_get(v___y_536_, 2);
lean_inc_ref(v_options_544_);
lean_inc_ref(v_lctx_543_);
v___x_545_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_545_, 0, v_env_540_);
lean_ctor_set(v___x_545_, 1, v_mctx_542_);
lean_ctor_set(v___x_545_, 2, v_lctx_543_);
lean_ctor_set(v___x_545_, 3, v_options_544_);
v___x_546_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v_msgData_533_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16___boxed(lean_object* v_msgData_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msgData_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_ref_561_; lean_object* v___x_562_; lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
v_ref_561_ = lean_ctor_get(v___y_558_, 5);
v___x_562_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_571_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v___x_569_; 
lean_inc(v_ref_561_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_ref_561_);
lean_ctor_set(v___x_567_, 1, v_a_563_);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 1);
lean_ctor_set(v___x_565_, 0, v___x_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg___boxed(lean_object* v_msg_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(lean_object* v_ref_579_, lean_object* v_msg_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_fileName_589_; lean_object* v_fileMap_590_; lean_object* v_options_591_; lean_object* v_currRecDepth_592_; lean_object* v_maxRecDepth_593_; lean_object* v_ref_594_; lean_object* v_currNamespace_595_; lean_object* v_openDecls_596_; lean_object* v_initHeartbeats_597_; lean_object* v_maxHeartbeats_598_; lean_object* v_quotContext_599_; lean_object* v_currMacroScope_600_; uint8_t v_diag_601_; lean_object* v_cancelTk_x3f_602_; uint8_t v_suppressElabErrors_603_; lean_object* v_inheritedTraceOptions_604_; lean_object* v_ref_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_fileName_589_ = lean_ctor_get(v___y_586_, 0);
v_fileMap_590_ = lean_ctor_get(v___y_586_, 1);
v_options_591_ = lean_ctor_get(v___y_586_, 2);
v_currRecDepth_592_ = lean_ctor_get(v___y_586_, 3);
v_maxRecDepth_593_ = lean_ctor_get(v___y_586_, 4);
v_ref_594_ = lean_ctor_get(v___y_586_, 5);
v_currNamespace_595_ = lean_ctor_get(v___y_586_, 6);
v_openDecls_596_ = lean_ctor_get(v___y_586_, 7);
v_initHeartbeats_597_ = lean_ctor_get(v___y_586_, 8);
v_maxHeartbeats_598_ = lean_ctor_get(v___y_586_, 9);
v_quotContext_599_ = lean_ctor_get(v___y_586_, 10);
v_currMacroScope_600_ = lean_ctor_get(v___y_586_, 11);
v_diag_601_ = lean_ctor_get_uint8(v___y_586_, sizeof(void*)*14);
v_cancelTk_x3f_602_ = lean_ctor_get(v___y_586_, 12);
v_suppressElabErrors_603_ = lean_ctor_get_uint8(v___y_586_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_604_ = lean_ctor_get(v___y_586_, 13);
v_ref_605_ = l_Lean_replaceRef(v_ref_579_, v_ref_594_);
lean_inc_ref(v_inheritedTraceOptions_604_);
lean_inc(v_cancelTk_x3f_602_);
lean_inc(v_currMacroScope_600_);
lean_inc(v_quotContext_599_);
lean_inc(v_maxHeartbeats_598_);
lean_inc(v_initHeartbeats_597_);
lean_inc(v_openDecls_596_);
lean_inc(v_currNamespace_595_);
lean_inc(v_maxRecDepth_593_);
lean_inc(v_currRecDepth_592_);
lean_inc_ref(v_options_591_);
lean_inc_ref(v_fileMap_590_);
lean_inc_ref(v_fileName_589_);
v___x_606_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_606_, 0, v_fileName_589_);
lean_ctor_set(v___x_606_, 1, v_fileMap_590_);
lean_ctor_set(v___x_606_, 2, v_options_591_);
lean_ctor_set(v___x_606_, 3, v_currRecDepth_592_);
lean_ctor_set(v___x_606_, 4, v_maxRecDepth_593_);
lean_ctor_set(v___x_606_, 5, v_ref_605_);
lean_ctor_set(v___x_606_, 6, v_currNamespace_595_);
lean_ctor_set(v___x_606_, 7, v_openDecls_596_);
lean_ctor_set(v___x_606_, 8, v_initHeartbeats_597_);
lean_ctor_set(v___x_606_, 9, v_maxHeartbeats_598_);
lean_ctor_set(v___x_606_, 10, v_quotContext_599_);
lean_ctor_set(v___x_606_, 11, v_currMacroScope_600_);
lean_ctor_set(v___x_606_, 12, v_cancelTk_x3f_602_);
lean_ctor_set(v___x_606_, 13, v_inheritedTraceOptions_604_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*14, v_diag_601_);
lean_ctor_set_uint8(v___x_606_, sizeof(void*)*14 + 1, v_suppressElabErrors_603_);
v___x_607_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_580_, v___y_584_, v___y_585_, v___x_606_, v___y_587_);
lean_dec_ref(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg___boxed(lean_object* v_ref_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_608_, v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec(v_ref_608_);
return v_res_618_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_619_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
lean_ctor_set(v___x_624_, 2, v___x_623_);
lean_ctor_set(v___x_624_, 3, v___x_623_);
lean_ctor_set(v___x_624_, 4, v___x_622_);
lean_ctor_set(v___x_624_, 5, v___x_622_);
lean_ctor_set(v___x_624_, 6, v___x_622_);
lean_ctor_set(v___x_624_, 7, v___x_622_);
lean_ctor_set(v___x_624_, 8, v___x_622_);
lean_ctor_set(v___x_624_, 9, v___x_622_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = lean_unsigned_to_nat(32u);
v___x_626_ = lean_mk_empty_array_with_capacity(v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_628_ = ((size_t)5ULL);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_unsigned_to_nat(32u);
v___x_631_ = lean_mk_empty_array_with_capacity(v___x_630_);
v___x_632_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_633_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
lean_ctor_set(v___x_633_, 2, v___x_629_);
lean_ctor_set(v___x_633_, 3, v___x_629_);
lean_ctor_set_usize(v___x_633_, 4, v___x_628_);
return v___x_633_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_634_ = lean_box(1);
v___x_635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_635_);
lean_ctor_set(v___x_637_, 2, v___x_634_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_655_ = l_Lean_stringToMessageData(v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_659_, lean_object* v_declHint_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___x_663_; lean_object* v_env_664_; uint8_t v___x_665_; 
v___x_663_ = lean_st_ref_get(v___y_661_);
v_env_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc_ref(v_env_664_);
lean_dec(v___x_663_);
v___x_665_ = l_Lean_Name_isAnonymous(v_declHint_660_);
if (v___x_665_ == 0)
{
uint8_t v_isExporting_666_; 
v_isExporting_666_ = lean_ctor_get_uint8(v_env_664_, sizeof(void*)*8);
if (v_isExporting_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_env_664_);
lean_dec(v_declHint_660_);
v___x_667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_667_, 0, v_msg_659_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; uint8_t v___x_669_; 
lean_inc_ref(v_env_664_);
v___x_668_ = l_Lean_Environment_setExporting(v_env_664_, v___x_665_);
lean_inc(v_declHint_660_);
lean_inc_ref(v___x_668_);
v___x_669_ = l_Lean_Environment_contains(v___x_668_, v_declHint_660_, v_isExporting_666_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec_ref(v___x_668_);
lean_dec_ref(v_env_664_);
lean_dec(v_declHint_660_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_msg_659_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v_c_676_; lean_object* v___x_677_; 
v___x_671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_672_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_673_ = l_Lean_Options_empty;
v___x_674_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_674_, 0, v___x_668_);
lean_ctor_set(v___x_674_, 1, v___x_671_);
lean_ctor_set(v___x_674_, 2, v___x_672_);
lean_ctor_set(v___x_674_, 3, v___x_673_);
lean_inc(v_declHint_660_);
v___x_675_ = l_Lean_MessageData_ofConstName(v_declHint_660_, v___x_665_);
v_c_676_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_676_, 0, v___x_674_);
lean_ctor_set(v_c_676_, 1, v___x_675_);
v___x_677_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_664_, v_declHint_660_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
lean_dec_ref(v_env_664_);
lean_dec(v_declHint_660_);
v___x_678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
lean_ctor_set(v___x_679_, 1, v_c_676_);
v___x_680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v___x_682_ = l_Lean_MessageData_note(v___x_681_);
v___x_683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_683_, 0, v_msg_659_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_720_; 
v_val_685_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_720_ == 0)
{
v___x_687_ = v___x_677_;
v_isShared_688_ = v_isSharedCheck_720_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v___x_677_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_720_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v_mod_692_; uint8_t v___x_693_; 
v___x_689_ = lean_box(0);
v___x_690_ = l_Lean_Environment_header(v_env_664_);
lean_dec_ref(v_env_664_);
v___x_691_ = l_Lean_EnvironmentHeader_moduleNames(v___x_690_);
v_mod_692_ = lean_array_get(v___x_689_, v___x_691_, v_val_685_);
lean_dec(v_val_685_);
lean_dec_ref(v___x_691_);
v___x_693_ = l_Lean_isPrivateName(v_declHint_660_);
lean_dec(v_declHint_660_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_694_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_c_676_);
v___x_696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
v___x_698_ = l_Lean_MessageData_ofName(v_mod_692_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Lean_MessageData_note(v___x_701_);
v___x_703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_703_, 0, v_msg_659_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 0);
lean_ctor_set(v___x_687_, 0, v___x_703_);
v___x_705_ = v___x_687_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_718_; 
v___x_707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
lean_ctor_set(v___x_708_, 1, v_c_676_);
v___x_709_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___x_711_ = l_Lean_MessageData_ofName(v_mod_692_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_712_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___x_715_ = l_Lean_MessageData_note(v___x_714_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v_msg_659_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
if (v_isShared_688_ == 0)
{
lean_ctor_set_tag(v___x_687_, 0);
lean_ctor_set(v___x_687_, 0, v___x_716_);
v___x_718_ = v___x_687_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_721_; 
lean_dec_ref(v_env_664_);
lean_dec(v_declHint_660_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_msg_659_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_722_, lean_object* v_declHint_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_722_, v_declHint_723_, v___y_724_);
lean_dec(v___y_724_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(lean_object* v_msg_727_, lean_object* v_declHint_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v___x_737_; lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_747_; 
v___x_737_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_727_, v_declHint_728_, v___y_735_);
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_747_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_747_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_742_ = l_Lean_unknownIdentifierMessageTag;
v___x_743_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_a_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_743_);
v___x_745_ = v___x_740_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12___boxed(lean_object* v_msg_748_, lean_object* v_declHint_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_748_, v_declHint_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_ref_759_, lean_object* v_msg_760_, lean_object* v_declHint_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v___x_770_; lean_object* v_a_771_; lean_object* v___x_772_; 
v___x_770_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12(v_msg_760_, v_declHint_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_759_, v_a_771_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_ref_773_, lean_object* v_msg_774_, lean_object* v_declHint_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_773_, v_msg_774_, v_declHint_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec(v_ref_773_);
return v_res_784_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__0));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__2));
v___x_790_ = l_Lean_stringToMessageData(v___x_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(lean_object* v_ref_791_, lean_object* v_constName_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_801_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__1);
v___x_802_ = 0;
lean_inc(v_constName_792_);
v___x_803_ = l_Lean_MessageData_ofConstName(v_constName_792_, v___x_802_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_801_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___closed__3);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_791_, v___x_806_, v_constName_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg___boxed(lean_object* v_ref_808_, lean_object* v_constName_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_808_, v_constName_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v_ref_808_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(lean_object* v_constName_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v_ref_828_; lean_object* v___x_829_; 
v_ref_828_ = lean_ctor_get(v___y_825_, 5);
v___x_829_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_828_, v_constName_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_constName_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(lean_object* v_constName_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___x_849_; lean_object* v_env_850_; uint8_t v___x_851_; lean_object* v___x_852_; 
v___x_849_ = lean_st_ref_get(v___y_847_);
v_env_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc_ref(v_env_850_);
lean_dec(v___x_849_);
v___x_851_ = 0;
lean_inc(v_constName_840_);
v___x_852_ = l_Lean_Environment_find_x3f(v_env_850_, v_constName_840_, v___x_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v___x_853_; 
v___x_853_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
return v___x_853_;
}
else
{
lean_object* v_val_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v_constName_840_);
v_val_854_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_852_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_val_854_);
lean_dec(v___x_852_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 0);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_val_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2___boxed(lean_object* v_constName_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_constName_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___y_863_);
return v_res_871_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0(void){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_instMonadEIO(lean_box(0));
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(lean_object* v_msg_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v_toApplicative_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_952_; 
v___x_886_ = lean_obj_once(&l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0, &l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0_once, _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__0);
v___x_887_ = l_StateRefT_x27_instMonad___redArg(v___x_886_);
v_toApplicative_888_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_952_ == 0)
{
lean_object* v_unused_953_; 
v_unused_953_ = lean_ctor_get(v___x_887_, 1);
lean_dec(v_unused_953_);
v___x_890_ = v___x_887_;
v_isShared_891_ = v_isSharedCheck_952_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_toApplicative_888_);
lean_dec(v___x_887_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_952_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v_toFunctor_892_; lean_object* v_toSeq_893_; lean_object* v_toSeqLeft_894_; lean_object* v_toSeqRight_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_950_; 
v_toFunctor_892_ = lean_ctor_get(v_toApplicative_888_, 0);
v_toSeq_893_ = lean_ctor_get(v_toApplicative_888_, 2);
v_toSeqLeft_894_ = lean_ctor_get(v_toApplicative_888_, 3);
v_toSeqRight_895_ = lean_ctor_get(v_toApplicative_888_, 4);
v_isSharedCheck_950_ = !lean_is_exclusive(v_toApplicative_888_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_toApplicative_888_, 1);
lean_dec(v_unused_951_);
v___x_897_ = v_toApplicative_888_;
v_isShared_898_ = v_isSharedCheck_950_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_toSeqRight_895_);
lean_inc(v_toSeqLeft_894_);
lean_inc(v_toSeq_893_);
lean_inc(v_toFunctor_892_);
lean_dec(v_toApplicative_888_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_950_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___f_899_; lean_object* v___f_900_; lean_object* v___f_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___f_905_; lean_object* v___f_906_; lean_object* v___x_908_; 
v___f_899_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__1));
v___f_900_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__2));
lean_inc_ref(v_toFunctor_892_);
v___f_901_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_901_, 0, v_toFunctor_892_);
v___f_902_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_902_, 0, v_toFunctor_892_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___f_901_);
lean_ctor_set(v___x_903_, 1, v___f_902_);
v___f_904_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_904_, 0, v_toSeqRight_895_);
v___f_905_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_905_, 0, v_toSeqLeft_894_);
v___f_906_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_906_, 0, v_toSeq_893_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 4, v___f_904_);
lean_ctor_set(v___x_897_, 3, v___f_905_);
lean_ctor_set(v___x_897_, 2, v___f_906_);
lean_ctor_set(v___x_897_, 1, v___f_899_);
lean_ctor_set(v___x_897_, 0, v___x_903_);
v___x_908_ = v___x_897_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___f_899_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v___f_906_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v___f_905_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___f_904_);
v___x_908_ = v_reuseFailAlloc_949_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 1, v___f_900_);
lean_ctor_set(v___x_890_, 0, v___x_908_);
v___x_910_ = v___x_890_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___f_900_);
v___x_910_ = v_reuseFailAlloc_948_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_911_; lean_object* v_toApplicative_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_946_; 
v___x_911_ = l_StateRefT_x27_instMonad___redArg(v___x_910_);
v_toApplicative_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_946_ == 0)
{
lean_object* v_unused_947_; 
v_unused_947_ = lean_ctor_get(v___x_911_, 1);
lean_dec(v_unused_947_);
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_946_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_toApplicative_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_946_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_toFunctor_916_; lean_object* v_toSeq_917_; lean_object* v_toSeqLeft_918_; lean_object* v_toSeqRight_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_944_; 
v_toFunctor_916_ = lean_ctor_get(v_toApplicative_912_, 0);
v_toSeq_917_ = lean_ctor_get(v_toApplicative_912_, 2);
v_toSeqLeft_918_ = lean_ctor_get(v_toApplicative_912_, 3);
v_toSeqRight_919_ = lean_ctor_get(v_toApplicative_912_, 4);
v_isSharedCheck_944_ = !lean_is_exclusive(v_toApplicative_912_);
if (v_isSharedCheck_944_ == 0)
{
lean_object* v_unused_945_; 
v_unused_945_ = lean_ctor_get(v_toApplicative_912_, 1);
lean_dec(v_unused_945_);
v___x_921_ = v_toApplicative_912_;
v_isShared_922_ = v_isSharedCheck_944_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_toSeqRight_919_);
lean_inc(v_toSeqLeft_918_);
lean_inc(v_toSeq_917_);
lean_inc(v_toFunctor_916_);
lean_dec(v_toApplicative_912_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_944_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___f_923_; lean_object* v___f_924_; lean_object* v___f_925_; lean_object* v___f_926_; lean_object* v___x_927_; lean_object* v___f_928_; lean_object* v___f_929_; lean_object* v___f_930_; lean_object* v___x_932_; 
v___f_923_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__3));
v___f_924_ = ((lean_object*)(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___closed__4));
lean_inc_ref(v_toFunctor_916_);
v___f_925_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_925_, 0, v_toFunctor_916_);
v___f_926_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_926_, 0, v_toFunctor_916_);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___f_925_);
lean_ctor_set(v___x_927_, 1, v___f_926_);
v___f_928_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_928_, 0, v_toSeqRight_919_);
v___f_929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_929_, 0, v_toSeqLeft_918_);
v___f_930_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_930_, 0, v_toSeq_917_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 4, v___f_928_);
lean_ctor_set(v___x_921_, 3, v___f_929_);
lean_ctor_set(v___x_921_, 2, v___f_930_);
lean_ctor_set(v___x_921_, 1, v___f_923_);
lean_ctor_set(v___x_921_, 0, v___x_927_);
v___x_932_ = v___x_921_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_927_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___f_923_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v___f_930_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v___f_929_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v___f_928_);
v___x_932_ = v_reuseFailAlloc_943_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 1, v___f_924_);
lean_ctor_set(v___x_914_, 0, v___x_932_);
v___x_934_ = v___x_914_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___f_924_);
v___x_934_ = v_reuseFailAlloc_942_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_13749__overap_940_; lean_object* v___x_941_; 
v___x_935_ = l_StateRefT_x27_instMonad___redArg(v___x_934_);
v___x_936_ = l_ReaderT_instMonad___redArg(v___x_935_);
v___x_937_ = l_ReaderT_instMonad___redArg(v___x_936_);
v___x_938_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_939_ = l_instInhabitedOfMonad___redArg(v___x_937_, v___x_938_);
v___x_13749__overap_940_ = lean_panic_fn_borrowed(v___x_939_, v_msg_877_);
lean_dec(v___x_939_);
lean_inc(v___y_884_);
lean_inc_ref(v___y_883_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
v___x_941_ = lean_apply_8(v___x_13749__overap_940_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, lean_box(0));
return v___x_941_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3___boxed(lean_object* v_msg_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v_msg_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
return v_res_963_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__2));
v___x_968_ = lean_unsigned_to_nat(53u);
v___x_969_ = lean_unsigned_to_nat(62u);
v___x_970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__1));
v___x_971_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__0));
v___x_972_ = l_mkPanicMessageWithDecl(v___x_971_, v___x_970_, v___x_969_, v___x_968_, v___x_967_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(size_t v_sz_973_, size_t v_i_974_, lean_object* v_bs_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
uint8_t v___x_984_; 
v___x_984_ = lean_usize_dec_lt(v_i_974_, v_sz_973_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v_bs_975_);
return v___x_985_;
}
else
{
lean_object* v_v_986_; lean_object* v___x_987_; 
v_v_986_ = lean_array_uget_borrowed(v_bs_975_, v_i_974_);
lean_inc(v_v_986_);
v___x_987_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_v_986_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; lean_object* v___x_989_; lean_object* v_bs_x27_990_; lean_object* v_a_992_; 
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = lean_unsigned_to_nat(0u);
v_bs_x27_990_ = lean_array_uset(v_bs_975_, v_i_974_, v___x_989_);
if (lean_obj_tag(v_a_988_) == 6)
{
lean_object* v_val_997_; lean_object* v_numFields_998_; uint8_t v___x_999_; lean_object* v___x_1000_; 
v_val_997_ = lean_ctor_get(v_a_988_, 0);
lean_inc_ref(v_val_997_);
lean_dec_ref(v_a_988_);
v_numFields_998_ = lean_ctor_get(v_val_997_, 4);
lean_inc(v_numFields_998_);
lean_dec_ref(v_val_997_);
v___x_999_ = 0;
v___x_1000_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1000_, 0, v_numFields_998_);
lean_ctor_set(v___x_1000_, 1, v___x_989_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*2, v___x_999_);
v_a_992_ = v___x_1000_;
goto v___jp_991_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_dec(v_a_988_);
v___x_1001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___closed__3);
v___x_1002_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__3(v___x_1001_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref(v___x_1002_);
v_a_992_ = v_a_1003_;
goto v___jp_991_;
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_bs_x27_990_);
v_a_1004_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1002_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1002_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
v___jp_991_:
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((size_t)1ULL);
v___x_994_ = lean_usize_add(v_i_974_, v___x_993_);
v___x_995_ = lean_array_uset(v_bs_x27_990_, v_i_974_, v_a_992_);
v_i_974_ = v___x_994_;
v_bs_975_ = v___x_995_;
goto _start;
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_bs_975_);
v_a_1012_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_987_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_987_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5___boxed(lean_object* v_sz_1020_, lean_object* v_i_1021_, lean_object* v_bs_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
size_t v_sz_boxed_1031_; size_t v_i_boxed_1032_; lean_object* v_res_1033_; 
v_sz_boxed_1031_ = lean_unbox_usize(v_sz_1020_);
lean_dec(v_sz_1020_);
v_i_boxed_1032_ = lean_unbox_usize(v_i_1021_);
lean_dec(v_i_1021_);
v_res_1033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_boxed_1031_, v_i_boxed_1032_, v_bs_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(lean_object* v_declName_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v_env_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1037_ = lean_st_ref_get(v___y_1035_);
v_env_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc_ref(v_env_1038_);
lean_dec(v___x_1037_);
v___x_1039_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1038_, v_declName_1034_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg___boxed(lean_object* v_declName_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1041_, v___y_1042_);
lean_dec(v___y_1042_);
return v_res_1044_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1045_; lean_object* v_dummy_1046_; 
v___x_1045_ = lean_box(0);
v_dummy_1046_ = l_Lean_Expr_sort___override(v___x_1045_);
return v_dummy_1046_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_unsigned_to_nat(16u);
v___x_1049_ = lean_mk_array(v___x_1048_, v___x_1047_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1050_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__1);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(lean_object* v_e_1055_, uint8_t v_alsoCasesOn_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_Expr_isApp(v_e_1055_);
if (v___x_1068_ == 0)
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec_ref(v_e_1055_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_Expr_getAppFn(v_e_1055_);
if (lean_obj_tag(v___x_1071_) == 4)
{
lean_object* v_declName_1072_; lean_object* v_us_1073_; lean_object* v___x_1074_; lean_object* v_a_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1229_; 
v_declName_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc_n(v_declName_1072_, 2);
v_us_1073_ = lean_ctor_get(v___x_1071_, 1);
lean_inc(v_us_1073_);
lean_dec_ref(v___x_1071_);
v___x_1074_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1072_, v___y_1063_);
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1077_ = v___x_1074_;
v_isShared_1078_ = v_isSharedCheck_1229_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_a_1075_);
lean_dec(v___x_1074_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1229_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
if (lean_obj_tag(v_a_1075_) == 1)
{
lean_object* v_val_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1121_; 
v_val_1079_ = lean_ctor_get(v_a_1075_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_1075_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1081_ = v_a_1075_;
v_isShared_1082_ = v_isSharedCheck_1121_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_val_1079_);
lean_dec(v_a_1075_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1121_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_dummy_1083_; lean_object* v_nargs_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_args_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v_dummy_1083_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_1084_ = l_Lean_Expr_getAppNumArgs(v_e_1055_);
lean_inc(v_nargs_1084_);
v___x_1085_ = lean_mk_array(v_nargs_1084_, v_dummy_1083_);
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_sub(v_nargs_1084_, v___x_1086_);
lean_dec(v_nargs_1084_);
v_args_1088_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1055_, v___x_1085_, v___x_1087_);
v___x_1089_ = lean_array_get_size(v_args_1088_);
v___x_1090_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1079_);
v___x_1091_ = lean_nat_dec_lt(v___x_1089_, v___x_1090_);
lean_dec(v___x_1090_);
if (v___x_1091_ == 0)
{
lean_object* v_numParams_1092_; lean_object* v_numDiscrs_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1112_; 
v_numParams_1092_ = lean_ctor_get(v_val_1079_, 0);
v_numDiscrs_1093_ = lean_ctor_get(v_val_1079_, 1);
v___x_1094_ = lean_array_mk(v_us_1073_);
v___x_1095_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1092_);
v___x_1096_ = l_Array_extract___redArg(v_args_1088_, v___x_1095_, v_numParams_1092_);
v___x_1097_ = l_Lean_instInhabitedExpr;
v___x_1098_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1079_);
v___x_1099_ = lean_array_get(v___x_1097_, v_args_1088_, v___x_1098_);
lean_dec(v___x_1098_);
v___x_1100_ = lean_nat_add(v_numParams_1092_, v___x_1086_);
v___x_1101_ = lean_nat_add(v___x_1100_, v_numDiscrs_1093_);
lean_inc(v___x_1101_);
lean_inc_ref_n(v_args_1088_, 2);
v___x_1102_ = l_Array_toSubarray___redArg(v_args_1088_, v___x_1100_, v___x_1101_);
v___x_1103_ = l_Subarray_copy___redArg(v___x_1102_);
v___x_1104_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1079_);
v___x_1105_ = lean_nat_add(v___x_1101_, v___x_1104_);
lean_dec(v___x_1104_);
lean_inc(v___x_1105_);
v___x_1106_ = l_Array_toSubarray___redArg(v_args_1088_, v___x_1101_, v___x_1105_);
v___x_1107_ = l_Subarray_copy___redArg(v___x_1106_);
v___x_1108_ = l_Array_toSubarray___redArg(v_args_1088_, v___x_1105_, v___x_1089_);
v___x_1109_ = l_Subarray_copy___redArg(v___x_1108_);
v___x_1110_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1110_, 0, v_val_1079_);
lean_ctor_set(v___x_1110_, 1, v_declName_1072_);
lean_ctor_set(v___x_1110_, 2, v___x_1094_);
lean_ctor_set(v___x_1110_, 3, v___x_1096_);
lean_ctor_set(v___x_1110_, 4, v___x_1099_);
lean_ctor_set(v___x_1110_, 5, v___x_1103_);
lean_ctor_set(v___x_1110_, 6, v___x_1107_);
lean_ctor_set(v___x_1110_, 7, v___x_1109_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v___x_1110_);
v___x_1112_ = v___x_1081_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1112_);
v___x_1114_ = v___x_1077_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1119_; 
lean_dec_ref(v_args_1088_);
lean_del_object(v___x_1081_);
lean_dec(v_val_1079_);
lean_dec(v_us_1073_);
lean_dec(v_declName_1072_);
v___x_1117_ = lean_box(0);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1117_);
v___x_1119_ = v___x_1077_;
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
}
else
{
lean_object* v___x_1122_; 
lean_del_object(v___x_1077_);
lean_dec(v_a_1075_);
v___x_1122_ = lean_st_ref_get(v___y_1063_);
if (v_alsoCasesOn_1056_ == 0)
{
lean_dec(v___x_1122_);
lean_dec(v_us_1073_);
lean_dec(v_declName_1072_);
lean_dec_ref(v_e_1055_);
goto v___jp_1065_;
}
else
{
lean_object* v_env_1123_; uint8_t v___x_1124_; 
v_env_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_env_1123_);
lean_dec(v___x_1122_);
lean_inc(v_declName_1072_);
v___x_1124_ = l_Lean_isCasesOnRecursor(v_env_1123_, v_declName_1072_);
if (v___x_1124_ == 0)
{
lean_dec(v_us_1073_);
lean_dec(v_declName_1072_);
lean_dec_ref(v_e_1055_);
goto v___jp_1065_;
}
else
{
lean_object* v_indName_1125_; lean_object* v___x_1126_; 
v_indName_1125_ = l_Lean_Name_getPrefix(v_declName_1072_);
v___x_1126_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2(v_indName_1125_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1220_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1220_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1220_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
if (lean_obj_tag(v_a_1127_) == 5)
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1215_; 
v_val_1131_ = lean_ctor_get(v_a_1127_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_a_1127_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1133_ = v_a_1127_;
v_isShared_1134_ = v_isSharedCheck_1215_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v_a_1127_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1215_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_toConstantVal_1135_; lean_object* v_numParams_1136_; lean_object* v_numIndices_1137_; lean_object* v_ctors_1138_; lean_object* v_nargs_1139_; lean_object* v_dummy_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v_args_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
v_toConstantVal_1135_ = lean_ctor_get(v_val_1131_, 0);
lean_inc_ref(v_toConstantVal_1135_);
v_numParams_1136_ = lean_ctor_get(v_val_1131_, 1);
lean_inc(v_numParams_1136_);
v_numIndices_1137_ = lean_ctor_get(v_val_1131_, 2);
lean_inc(v_numIndices_1137_);
v_ctors_1138_ = lean_ctor_get(v_val_1131_, 4);
lean_inc(v_ctors_1138_);
v_nargs_1139_ = l_Lean_Expr_getAppNumArgs(v_e_1055_);
v_dummy_1140_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
lean_inc(v_nargs_1139_);
v___x_1141_ = lean_mk_array(v_nargs_1139_, v_dummy_1140_);
v___x_1142_ = lean_unsigned_to_nat(1u);
v___x_1143_ = lean_nat_sub(v_nargs_1139_, v___x_1142_);
lean_dec(v_nargs_1139_);
v_args_1144_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1055_, v___x_1141_, v___x_1143_);
v___x_1145_ = lean_nat_add(v_numParams_1136_, v___x_1142_);
v___x_1146_ = lean_nat_add(v___x_1145_, v_numIndices_1137_);
v___x_1147_ = lean_nat_add(v___x_1146_, v___x_1142_);
lean_dec(v___x_1146_);
v___x_1148_ = l_Lean_InductiveVal_numCtors(v_val_1131_);
lean_dec_ref(v_val_1131_);
v___x_1149_ = lean_nat_add(v___x_1147_, v___x_1148_);
lean_dec(v___x_1148_);
v___x_1150_ = lean_array_get_size(v_args_1144_);
v___x_1151_ = lean_nat_dec_le(v___x_1149_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_dec(v___x_1149_);
lean_dec(v___x_1147_);
lean_dec(v___x_1145_);
lean_dec_ref(v_args_1144_);
lean_dec(v_ctors_1138_);
lean_dec(v_numIndices_1137_);
lean_dec(v_numParams_1136_);
lean_dec_ref(v_toConstantVal_1135_);
lean_del_object(v___x_1133_);
lean_dec(v_us_1073_);
lean_dec(v_declName_1072_);
v___x_1152_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1152_);
v___x_1154_ = v___x_1129_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
lean_object* v___x_1156_; lean_object* v_params_1157_; lean_object* v___x_1158_; lean_object* v_motive_1159_; lean_object* v_discrs_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_discrInfos_1163_; lean_object* v_alts_1164_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v_lower_1206_; lean_object* v_upper_1207_; uint8_t v___x_1214_; 
lean_del_object(v___x_1129_);
v___x_1156_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1136_);
lean_inc_ref_n(v_args_1144_, 3);
v_params_1157_ = l_Array_toSubarray___redArg(v_args_1144_, v___x_1156_, v_numParams_1136_);
v___x_1158_ = l_Lean_instInhabitedExpr;
v_motive_1159_ = lean_array_get(v___x_1158_, v_args_1144_, v_numParams_1136_);
lean_dec(v_numParams_1136_);
lean_inc(v___x_1147_);
v_discrs_1160_ = l_Array_toSubarray___redArg(v_args_1144_, v___x_1145_, v___x_1147_);
v___x_1161_ = lean_nat_add(v_numIndices_1137_, v___x_1142_);
lean_dec(v_numIndices_1137_);
v___x_1162_ = lean_box(0);
v_discrInfos_1163_ = lean_mk_array(v___x_1161_, v___x_1162_);
lean_inc(v___x_1149_);
v_alts_1164_ = l_Array_toSubarray___redArg(v_args_1144_, v___x_1147_, v___x_1149_);
v___x_1214_ = lean_nat_dec_le(v___x_1149_, v___x_1156_);
if (v___x_1214_ == 0)
{
v_lower_1206_ = v___x_1149_;
v_upper_1207_ = v___x_1150_;
goto v___jp_1205_;
}
else
{
lean_dec(v___x_1149_);
v_lower_1206_ = v___x_1156_;
v_upper_1207_ = v___x_1150_;
goto v___jp_1205_;
}
v___jp_1165_:
{
lean_object* v___x_1168_; size_t v_sz_1169_; size_t v___x_1170_; lean_object* v___x_1171_; 
v___x_1168_ = lean_array_mk(v_ctors_1138_);
v_sz_1169_ = lean_array_size(v___x_1168_);
v___x_1170_ = ((size_t)0ULL);
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__5(v_sz_1169_, v___x_1170_, v___x_1168_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1196_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1174_ = v___x_1171_;
v_isShared_1175_ = v_isSharedCheck_1196_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1171_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1196_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v_start_1176_; lean_object* v_stop_1177_; lean_object* v_start_1178_; lean_object* v_stop_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v_start_1176_ = lean_ctor_get(v_params_1157_, 1);
lean_inc(v_start_1176_);
v_stop_1177_ = lean_ctor_get(v_params_1157_, 2);
lean_inc(v_stop_1177_);
v_start_1178_ = lean_ctor_get(v_discrs_1160_, 1);
lean_inc(v_start_1178_);
v_stop_1179_ = lean_ctor_get(v_discrs_1160_, 2);
lean_inc(v_stop_1179_);
v___x_1180_ = lean_nat_sub(v_stop_1177_, v_start_1176_);
lean_dec(v_start_1176_);
lean_dec(v_stop_1177_);
v___x_1181_ = lean_nat_sub(v_stop_1179_, v_start_1178_);
lean_dec(v_start_1178_);
lean_dec(v_stop_1179_);
v___x_1182_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__2);
v___x_1183_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1180_);
lean_ctor_set(v___x_1183_, 1, v___x_1181_);
lean_ctor_set(v___x_1183_, 2, v_a_1172_);
lean_ctor_set(v___x_1183_, 3, v___y_1167_);
lean_ctor_set(v___x_1183_, 4, v_discrInfos_1163_);
lean_ctor_set(v___x_1183_, 5, v___x_1182_);
v___x_1184_ = lean_array_mk(v_us_1073_);
v___x_1185_ = l_Subarray_copy___redArg(v_params_1157_);
v___x_1186_ = l_Subarray_copy___redArg(v_discrs_1160_);
v___x_1187_ = l_Subarray_copy___redArg(v_alts_1164_);
v___x_1188_ = l_Subarray_copy___redArg(v___y_1166_);
v___x_1189_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1183_);
lean_ctor_set(v___x_1189_, 1, v_declName_1072_);
lean_ctor_set(v___x_1189_, 2, v___x_1184_);
lean_ctor_set(v___x_1189_, 3, v___x_1185_);
lean_ctor_set(v___x_1189_, 4, v_motive_1159_);
lean_ctor_set(v___x_1189_, 5, v___x_1186_);
lean_ctor_set(v___x_1189_, 6, v___x_1187_);
lean_ctor_set(v___x_1189_, 7, v___x_1188_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 1);
lean_ctor_set(v___x_1133_, 0, v___x_1189_);
v___x_1191_ = v___x_1133_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1189_);
v___x_1191_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1193_; 
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 0, v___x_1191_);
v___x_1193_ = v___x_1174_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1191_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1166_);
lean_dec_ref(v_alts_1164_);
lean_dec_ref(v_discrInfos_1163_);
lean_dec_ref(v_discrs_1160_);
lean_dec(v_motive_1159_);
lean_dec_ref(v_params_1157_);
lean_del_object(v___x_1133_);
lean_dec(v_us_1073_);
lean_dec(v_declName_1072_);
v_a_1197_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1171_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1171_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
v___jp_1205_:
{
lean_object* v_levelParams_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; 
v_levelParams_1208_ = lean_ctor_get(v_toConstantVal_1135_, 1);
lean_inc(v_levelParams_1208_);
lean_dec_ref(v_toConstantVal_1135_);
v___x_1209_ = l_Array_toSubarray___redArg(v_args_1144_, v_lower_1206_, v_upper_1207_);
v___x_1210_ = l_List_lengthTR___redArg(v_levelParams_1208_);
lean_dec(v_levelParams_1208_);
v___x_1211_ = l_List_lengthTR___redArg(v_us_1073_);
v___x_1212_ = lean_nat_dec_eq(v___x_1210_, v___x_1211_);
lean_dec(v___x_1211_);
lean_dec(v___x_1210_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__3));
v___y_1166_ = v___x_1209_;
v___y_1167_ = v___x_1213_;
goto v___jp_1165_;
}
else
{
v___y_1166_ = v___x_1209_;
v___y_1167_ = v___x_1162_;
goto v___jp_1165_;
}
}
}
}
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
lean_dec(v_a_1127_);
lean_dec(v_us_1073_);
lean_dec(v_declName_1072_);
lean_dec_ref(v_e_1055_);
v___x_1216_ = lean_box(0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1216_);
v___x_1218_ = v___x_1129_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_us_1073_);
lean_dec(v_declName_1072_);
lean_dec_ref(v_e_1055_);
v_a_1221_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1126_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1126_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
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
lean_dec_ref(v___x_1071_);
lean_dec_ref(v_e_1055_);
goto v___jp_1065_;
}
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___boxed(lean_object* v_e_1230_, lean_object* v_alsoCasesOn_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_alsoCasesOn_boxed_1240_; lean_object* v_res_1241_; 
v_alsoCasesOn_boxed_1240_ = lean_unbox(v_alsoCasesOn_1231_);
v_res_1241_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1230_, v_alsoCasesOn_boxed_1240_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(size_t v_sz_1242_, size_t v_i_1243_, lean_object* v_bs_1244_){
_start:
{
uint8_t v___x_1245_; 
v___x_1245_ = lean_usize_dec_lt(v_i_1243_, v_sz_1242_);
if (v___x_1245_ == 0)
{
return v_bs_1244_;
}
else
{
lean_object* v_v_1246_; lean_object* v___x_1247_; lean_object* v_bs_x27_1248_; lean_object* v___y_1250_; lean_object* v___x_1255_; 
v_v_1246_ = lean_array_uget(v_bs_1244_, v_i_1243_);
v___x_1247_ = lean_unsigned_to_nat(0u);
v_bs_x27_1248_ = lean_array_uset(v_bs_1244_, v_i_1243_, v___x_1247_);
v___x_1255_ = l_Lean_Elab_WF_isWfParam_x3f(v_v_1246_);
if (lean_obj_tag(v___x_1255_) == 0)
{
v___y_1250_ = v_v_1246_;
goto v___jp_1249_;
}
else
{
lean_object* v_val_1256_; 
lean_dec(v_v_1246_);
v_val_1256_ = lean_ctor_get(v___x_1255_, 0);
lean_inc(v_val_1256_);
lean_dec_ref(v___x_1255_);
v___y_1250_ = v_val_1256_;
goto v___jp_1249_;
}
v___jp_1249_:
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1243_, v___x_1251_);
v___x_1253_ = lean_array_uset(v_bs_x27_1248_, v_i_1243_, v___y_1250_);
v_i_1243_ = v___x_1252_;
v_bs_1244_ = v___x_1253_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5___boxed(lean_object* v_sz_1257_, lean_object* v_i_1258_, lean_object* v_bs_1259_){
_start:
{
size_t v_sz_boxed_1260_; size_t v_i_boxed_1261_; lean_object* v_res_1262_; 
v_sz_boxed_1260_ = lean_unbox_usize(v_sz_1257_);
lean_dec(v_sz_1257_);
v_i_boxed_1261_ = lean_unbox_usize(v_i_1258_);
lean_dec(v_i_1258_);
v_res_1262_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_boxed_1260_, v_i_boxed_1261_, v_bs_1259_);
return v_res_1262_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(lean_object* v_as_1263_, size_t v_i_1264_, size_t v_stop_1265_){
_start:
{
uint8_t v___x_1266_; 
v___x_1266_ = lean_usize_dec_eq(v_i_1264_, v_stop_1265_);
if (v___x_1266_ == 0)
{
uint8_t v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = 1;
v___x_1268_ = lean_array_uget_borrowed(v_as_1263_, v_i_1264_);
v___x_1269_ = l_Lean_Elab_WF_isWfParam_x3f(v___x_1268_);
if (lean_obj_tag(v___x_1269_) == 0)
{
if (v___x_1266_ == 0)
{
size_t v___x_1270_; size_t v___x_1271_; 
v___x_1270_ = ((size_t)1ULL);
v___x_1271_ = lean_usize_add(v_i_1264_, v___x_1270_);
v_i_1264_ = v___x_1271_;
goto _start;
}
else
{
return v___x_1267_;
}
}
else
{
lean_dec_ref(v___x_1269_);
return v___x_1267_;
}
}
else
{
uint8_t v___x_1273_; 
v___x_1273_ = 0;
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3___boxed(lean_object* v_as_1274_, lean_object* v_i_1275_, lean_object* v_stop_1276_){
_start:
{
size_t v_i_boxed_1277_; size_t v_stop_boxed_1278_; uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_i_boxed_1277_ = lean_unbox_usize(v_i_1275_);
lean_dec(v_i_1275_);
v_stop_boxed_1278_ = lean_unbox_usize(v_stop_1276_);
lean_dec(v_stop_1276_);
v_res_1279_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_as_1274_, v_i_boxed_1277_, v_stop_boxed_1278_);
lean_dec_ref(v_as_1274_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher(lean_object* v_e_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
uint8_t v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = 1;
v___x_1291_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2(v_e_1281_, v___x_1290_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1354_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1354_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1354_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
if (lean_obj_tag(v_a_1292_) == 1)
{
lean_object* v_val_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1351_; 
v_val_1301_ = lean_ctor_get(v_a_1292_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_a_1292_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1303_ = v_a_1292_;
v_isShared_1304_ = v_isSharedCheck_1351_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_val_1301_);
lean_dec(v_a_1292_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1351_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v_toMatcherInfo_1305_; lean_object* v_matcherName_1306_; lean_object* v_matcherLevels_1307_; lean_object* v_params_1308_; lean_object* v_motive_1309_; lean_object* v_discrs_1310_; lean_object* v_alts_1311_; lean_object* v_remaining_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1350_; 
v_toMatcherInfo_1305_ = lean_ctor_get(v_val_1301_, 0);
v_matcherName_1306_ = lean_ctor_get(v_val_1301_, 1);
v_matcherLevels_1307_ = lean_ctor_get(v_val_1301_, 2);
v_params_1308_ = lean_ctor_get(v_val_1301_, 3);
v_motive_1309_ = lean_ctor_get(v_val_1301_, 4);
v_discrs_1310_ = lean_ctor_get(v_val_1301_, 5);
v_alts_1311_ = lean_ctor_get(v_val_1301_, 6);
v_remaining_1312_ = lean_ctor_get(v_val_1301_, 7);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_val_1301_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1314_ = v_val_1301_;
v_isShared_1315_ = v_isSharedCheck_1350_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_remaining_1312_);
lean_inc(v_alts_1311_);
lean_inc(v_discrs_1310_);
lean_inc(v_motive_1309_);
lean_inc(v_params_1308_);
lean_inc(v_matcherLevels_1307_);
lean_inc(v_matcherName_1306_);
lean_inc(v_toMatcherInfo_1305_);
lean_dec(v_val_1301_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1350_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_array_get_size(v_discrs_1310_);
v___x_1318_ = lean_nat_dec_lt(v___x_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_del_object(v___x_1314_);
lean_dec_ref(v_remaining_1312_);
lean_dec_ref(v_alts_1311_);
lean_dec_ref(v_discrs_1310_);
lean_dec_ref(v_motive_1309_);
lean_dec_ref(v_params_1308_);
lean_dec_ref(v_matcherLevels_1307_);
lean_dec(v_matcherName_1306_);
lean_dec_ref(v_toMatcherInfo_1305_);
lean_del_object(v___x_1303_);
goto v___jp_1296_;
}
else
{
if (v___x_1318_ == 0)
{
lean_del_object(v___x_1314_);
lean_dec_ref(v_remaining_1312_);
lean_dec_ref(v_alts_1311_);
lean_dec_ref(v_discrs_1310_);
lean_dec_ref(v_motive_1309_);
lean_dec_ref(v_params_1308_);
lean_dec_ref(v_matcherLevels_1307_);
lean_dec(v_matcherName_1306_);
lean_dec_ref(v_toMatcherInfo_1305_);
lean_del_object(v___x_1303_);
goto v___jp_1296_;
}
else
{
size_t v___x_1319_; size_t v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1317_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_WF_paramMatcher_spec__3(v_discrs_1310_, v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_del_object(v___x_1314_);
lean_dec_ref(v_remaining_1312_);
lean_dec_ref(v_alts_1311_);
lean_dec_ref(v_discrs_1310_);
lean_dec_ref(v_motive_1309_);
lean_dec_ref(v_params_1308_);
lean_dec_ref(v_matcherLevels_1307_);
lean_dec(v_matcherName_1306_);
lean_dec_ref(v_toMatcherInfo_1305_);
lean_del_object(v___x_1303_);
goto v___jp_1296_;
}
else
{
size_t v_sz_1322_; lean_object* v___x_1323_; 
lean_del_object(v___x_1294_);
v_sz_1322_ = lean_array_size(v_alts_1311_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__4(v_sz_1322_, v___x_1319_, v_alts_1311_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1341_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1341_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1341_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
size_t v_sz_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v_sz_1328_ = lean_array_size(v_discrs_1310_);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__5(v_sz_1328_, v___x_1319_, v_discrs_1310_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 6, v_a_1324_);
lean_ctor_set(v___x_1314_, 5, v___x_1329_);
v___x_1331_ = v___x_1314_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_toMatcherInfo_1305_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_matcherName_1306_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_matcherLevels_1307_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_params_1308_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_motive_1309_);
lean_ctor_set(v_reuseFailAlloc_1340_, 5, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1340_, 6, v_a_1324_);
lean_ctor_set(v_reuseFailAlloc_1340_, 7, v_remaining_1312_);
v___x_1331_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1332_ = l_Lean_Meta_MatcherApp_toExpr(v___x_1331_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 0, v___x_1332_);
v___x_1334_ = v___x_1303_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1335_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1335_);
v___x_1337_ = v___x_1326_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v___x_1335_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_del_object(v___x_1314_);
lean_dec_ref(v_remaining_1312_);
lean_dec_ref(v_discrs_1310_);
lean_dec_ref(v_motive_1309_);
lean_dec_ref(v_params_1308_);
lean_dec_ref(v_matcherLevels_1307_);
lean_dec(v_matcherName_1306_);
lean_dec_ref(v_toMatcherInfo_1305_);
lean_del_object(v___x_1303_);
v_a_1342_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1323_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1323_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
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
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_del_object(v___x_1294_);
lean_dec(v_a_1292_);
v___x_1352_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
return v___x_1353_;
}
v___jp_1296_:
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1297_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1297_);
v___x_1299_ = v___x_1294_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_a_1355_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1291_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1291_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___boxed(lean_object* v_e_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Elab_WF_paramMatcher(v_e_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(size_t v_sz_1373_, size_t v_i_1374_, lean_object* v_bs_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___redArg(v_sz_1373_, v_i_1374_, v_bs_1375_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0___boxed(lean_object* v_sz_1385_, lean_object* v_i_1386_, lean_object* v_bs_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
size_t v_sz_boxed_1396_; size_t v_i_boxed_1397_; lean_object* v_res_1398_; 
v_sz_boxed_1396_ = lean_unbox_usize(v_sz_1385_);
lean_dec(v_sz_1385_);
v_i_boxed_1397_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_res_1398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_paramMatcher_spec__0(v_sz_boxed_1396_, v_i_boxed_1397_, v_bs_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(lean_object* v_declName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___redArg(v_declName_1399_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4___boxed(lean_object* v_declName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__4(v_declName_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1410_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(lean_object* v_00_u03b1_1419_, lean_object* v_constName_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___redArg(v_constName_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_constName_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
lean_object* v_res_1440_; 
v_res_1440_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3(v_00_u03b1_1430_, v_constName_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(lean_object* v_00_u03b1_1441_, lean_object* v_ref_1442_, lean_object* v_constName_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___redArg(v_ref_1442_, v_constName_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9___boxed(lean_object* v_00_u03b1_1453_, lean_object* v_ref_1454_, lean_object* v_constName_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9(v_00_u03b1_1453_, v_ref_1454_, v_constName_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec(v_ref_1454_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_1465_, lean_object* v_ref_1466_, lean_object* v_msg_1467_, lean_object* v_declHint_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___redArg(v_ref_1466_, v_msg_1467_, v_declHint_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_ref_1479_, lean_object* v_msg_1480_, lean_object* v_declHint_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_1478_, v_ref_1479_, v_msg_1480_, v_declHint_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec(v_ref_1479_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(lean_object* v_msg_1491_, lean_object* v_declHint_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___redArg(v_msg_1491_, v_declHint_1492_, v___y_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1502_, lean_object* v_declHint_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__12_spec__13(v_msg_1502_, v_declHint_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(lean_object* v_00_u03b1_1513_, lean_object* v_ref_1514_, lean_object* v_msg_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___redArg(v_ref_1514_, v_msg_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1525_, lean_object* v_ref_1526_, lean_object* v_msg_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13(v_00_u03b1_1525_, v_ref_1526_, v_msg_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec(v_ref_1526_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(lean_object* v_00_u03b1_1537_, lean_object* v_msg_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___redArg(v_msg_1538_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15___boxed(lean_object* v_00_u03b1_1548_, lean_object* v_msg_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15(v_00_u03b1_1548_, v_msg_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1566_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1567_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1568_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1569_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1566_, v___x_1567_, v___x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12____boxed(lean_object* v_a_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
return v_res_1571_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramMatcher___boxed), 9, 0);
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_1576_ = 1;
v___x_1577_ = lean_obj_once(&l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_);
v___x_1578_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1575_, v___x_1576_, v___x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14____boxed(lean_object* v_a_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
return v_res_1580_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(lean_object* v_e_1581_){
_start:
{
if (lean_obj_tag(v_e_1581_) == 8)
{
lean_object* v_value_1582_; lean_object* v_body_1583_; lean_object* v___x_1584_; 
v_value_1582_ = lean_ctor_get(v_e_1581_, 2);
v_body_1583_ = lean_ctor_get(v_e_1581_, 3);
v___x_1584_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1582_);
if (lean_obj_tag(v___x_1584_) == 0)
{
v_e_1581_ = v_body_1583_;
goto _start;
}
else
{
uint8_t v___x_1586_; 
lean_dec_ref(v___x_1584_);
v___x_1586_ = 1;
return v___x_1586_;
}
}
else
{
uint8_t v___x_1587_; 
v___x_1587_ = 0;
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam___boxed(lean_object* v_e_1588_){
_start:
{
uint8_t v_res_1589_; lean_object* v_r_1590_; 
v_res_1589_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1588_);
lean_dec_ref(v_e_1588_);
v_r_1590_ = lean_box(v_res_1589_);
return v_r_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(lean_object* v_e_1591_, lean_object* v_acc_1592_){
_start:
{
if (lean_obj_tag(v_e_1591_) == 8)
{
lean_object* v_value_1593_; lean_object* v_body_1594_; lean_object* v___x_1595_; 
v_value_1593_ = lean_ctor_get(v_e_1591_, 2);
v_body_1594_ = lean_ctor_get(v_e_1591_, 3);
v___x_1595_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1593_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_unsigned_to_nat(1u);
v___x_1597_ = lean_nat_add(v_acc_1592_, v___x_1596_);
lean_dec(v_acc_1592_);
v_e_1591_ = v_body_1594_;
v_acc_1592_ = v___x_1597_;
goto _start;
}
else
{
lean_dec_ref(v___x_1595_);
return v_acc_1592_;
}
}
else
{
return v_acc_1592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam___boxed(lean_object* v_e_1599_, lean_object* v_acc_1600_){
_start:
{
lean_object* v_res_1601_; 
v_res_1601_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1599_, v_acc_1600_);
lean_dec_ref(v_e_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(lean_object* v_msg_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v___f_1609_; lean_object* v___x_1300__overap_1610_; lean_object* v___x_1611_; 
v___f_1609_ = ((lean_object*)(l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___closed__0));
v___x_1300__overap_1610_ = lean_panic_fn_borrowed(v___f_1609_, v_msg_1603_);
lean_inc(v___y_1607_);
lean_inc_ref(v___y_1606_);
lean_inc(v___y_1605_);
lean_inc_ref(v___y_1604_);
v___x_1611_ = lean_apply_5(v___x_1300__overap_1610_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, lean_box(0));
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0___boxed(lean_object* v_msg_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v_msg_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(lean_object* v_k_1619_, lean_object* v_b_1620_, lean_object* v_c_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_){
_start:
{
lean_object* v___x_1627_; 
lean_inc(v___y_1625_);
lean_inc_ref(v___y_1624_);
lean_inc(v___y_1623_);
lean_inc_ref(v___y_1622_);
v___x_1627_ = lean_apply_7(v_k_1619_, v_b_1620_, v_c_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, lean_box(0));
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed(lean_object* v_k_1628_, lean_object* v_b_1629_, lean_object* v_c_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0(v_k_1628_, v_b_1629_, v_c_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(lean_object* v_e_1637_, lean_object* v_maxFVars_x3f_1638_, lean_object* v_k_1639_, uint8_t v_cleanupAnnotations_1640_, uint8_t v_preserveNondepLet_1641_, uint8_t v_nondepLetOnly_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_){
_start:
{
lean_object* v___f_1648_; uint8_t v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; 
v___f_1648_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1648_, 0, v_k_1639_);
v___x_1649_ = 0;
v___x_1650_ = 1;
v___x_1651_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1637_, v___x_1649_, v___x_1650_, v_preserveNondepLet_1641_, v_nondepLetOnly_1642_, v_maxFVars_x3f_1638_, v___f_1648_, v_cleanupAnnotations_1640_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_a_1660_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1651_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1651_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___boxed(lean_object* v_e_1668_, lean_object* v_maxFVars_x3f_1669_, lean_object* v_k_1670_, lean_object* v_cleanupAnnotations_1671_, lean_object* v_preserveNondepLet_1672_, lean_object* v_nondepLetOnly_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1679_; uint8_t v_preserveNondepLet_boxed_1680_; uint8_t v_nondepLetOnly_boxed_1681_; lean_object* v_res_1682_; 
v_cleanupAnnotations_boxed_1679_ = lean_unbox(v_cleanupAnnotations_1671_);
v_preserveNondepLet_boxed_1680_ = lean_unbox(v_preserveNondepLet_1672_);
v_nondepLetOnly_boxed_1681_ = lean_unbox(v_nondepLetOnly_1673_);
v_res_1682_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1668_, v_maxFVars_x3f_1669_, v_k_1670_, v_cleanupAnnotations_boxed_1679_, v_preserveNondepLet_boxed_1680_, v_nondepLetOnly_boxed_1681_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v_maxFVars_x3f_1669_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(lean_object* v_00_u03b1_1683_, lean_object* v_e_1684_, lean_object* v_maxFVars_x3f_1685_, lean_object* v_k_1686_, uint8_t v_cleanupAnnotations_1687_, uint8_t v_preserveNondepLet_1688_, uint8_t v_nondepLetOnly_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1684_, v_maxFVars_x3f_1685_, v_k_1686_, v_cleanupAnnotations_1687_, v_preserveNondepLet_1688_, v_nondepLetOnly_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_e_1697_, lean_object* v_maxFVars_x3f_1698_, lean_object* v_k_1699_, lean_object* v_cleanupAnnotations_1700_, lean_object* v_preserveNondepLet_1701_, lean_object* v_nondepLetOnly_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1708_; uint8_t v_preserveNondepLet_boxed_1709_; uint8_t v_nondepLetOnly_boxed_1710_; lean_object* v_res_1711_; 
v_cleanupAnnotations_boxed_1708_ = lean_unbox(v_cleanupAnnotations_1700_);
v_preserveNondepLet_boxed_1709_ = lean_unbox(v_preserveNondepLet_1701_);
v_nondepLetOnly_boxed_1710_ = lean_unbox(v_nondepLetOnly_1702_);
v_res_1711_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1(v_00_u03b1_1696_, v_e_1697_, v_maxFVars_x3f_1698_, v_k_1699_, v_cleanupAnnotations_boxed_1708_, v_preserveNondepLet_boxed_1709_, v_nondepLetOnly_boxed_1710_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v_maxFVars_x3f_1698_);
return v_res_1711_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = l_Lean_Expr_bvar___override(v___x_1712_);
return v___x_1713_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4(void){
_start:
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1717_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__3));
v___x_1718_ = lean_unsigned_to_nat(6u);
v___x_1719_ = lean_unsigned_to_nat(138u);
v___x_1720_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__2));
v___x_1721_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__1));
v___x_1722_ = l_mkPanicMessageWithDecl(v___x_1721_, v___x_1720_, v___x_1719_, v___x_1718_, v___x_1717_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed(lean_object* v_xs_1723_, lean_object* v_b_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(v_xs_1723_, v_b_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec_ref(v_xs_1723_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(lean_object* v_e_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_){
_start:
{
if (lean_obj_tag(v_e_1731_) == 8)
{
lean_object* v_declName_1737_; lean_object* v_type_1738_; lean_object* v_value_1739_; lean_object* v_body_1740_; uint8_t v_nondep_1741_; lean_object* v___x_1742_; 
v_declName_1737_ = lean_ctor_get(v_e_1731_, 0);
v_type_1738_ = lean_ctor_get(v_e_1731_, 1);
v_value_1739_ = lean_ctor_get(v_e_1731_, 2);
v_body_1740_ = lean_ctor_get(v_e_1731_, 3);
v_nondep_1741_ = lean_ctor_get_uint8(v_e_1731_, sizeof(void*)*4 + 8);
v___x_1742_ = l_Lean_Elab_WF_isWfParam_x3f(v_value_1739_);
if (lean_obj_tag(v___x_1742_) == 1)
{
lean_object* v_val_1743_; lean_object* v___x_1744_; 
v_val_1743_ = lean_ctor_get(v___x_1742_, 0);
lean_inc(v_val_1743_);
lean_dec_ref(v___x_1742_);
lean_inc_ref(v_type_1738_);
v___x_1744_ = l_Lean_Meta_isProp(v_type_1738_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; uint8_t v___y_1747_; uint8_t v___x_1755_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref(v___x_1744_);
v___x_1755_ = lean_unbox(v_a_1745_);
lean_dec(v_a_1745_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_inc_ref(v_type_1738_);
v___x_1756_ = l_Lean_Meta_getLevel(v_type_1738_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___y_1766_; size_t v___x_1775_; uint8_t v___x_1776_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1756_);
v___x_1758_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_1759_ = lean_box(0);
v___x_1760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_a_1757_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = l_Lean_Expr_const___override(v___x_1758_, v___x_1760_);
v___x_1762_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__0);
lean_inc_ref(v_type_1738_);
v___x_1763_ = l_Lean_mkAppB(v___x_1761_, v_type_1738_, v___x_1762_);
v___x_1764_ = lean_expr_instantiate1(v_body_1740_, v___x_1763_);
lean_dec_ref(v___x_1763_);
v___x_1775_ = lean_ptr_addr(v_type_1738_);
v___x_1776_ = lean_usize_dec_eq(v___x_1775_, v___x_1775_);
if (v___x_1776_ == 0)
{
v___y_1766_ = v___x_1776_;
goto v___jp_1765_;
}
else
{
size_t v___x_1777_; size_t v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = lean_ptr_addr(v_value_1739_);
v___x_1778_ = lean_ptr_addr(v_val_1743_);
v___x_1779_ = lean_usize_dec_eq(v___x_1777_, v___x_1778_);
v___y_1766_ = v___x_1779_;
goto v___jp_1765_;
}
v___jp_1765_:
{
if (v___y_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_inc_ref(v_type_1738_);
lean_inc(v_declName_1737_);
lean_dec_ref(v_e_1731_);
v___x_1767_ = l_Lean_Expr_letE___override(v_declName_1737_, v_type_1738_, v_val_1743_, v___x_1764_, v_nondep_1741_);
v_e_1731_ = v___x_1767_;
goto _start;
}
else
{
size_t v___x_1769_; size_t v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_ptr_addr(v_body_1740_);
v___x_1770_ = lean_ptr_addr(v___x_1764_);
v___x_1771_ = lean_usize_dec_eq(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_inc_ref(v_type_1738_);
lean_inc(v_declName_1737_);
lean_dec_ref(v_e_1731_);
v___x_1772_ = l_Lean_Expr_letE___override(v_declName_1737_, v_type_1738_, v_val_1743_, v___x_1764_, v_nondep_1741_);
v_e_1731_ = v___x_1772_;
goto _start;
}
else
{
lean_dec_ref(v___x_1764_);
lean_dec(v_val_1743_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_val_1743_);
lean_dec_ref(v_e_1731_);
v_a_1780_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1756_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1756_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
size_t v___x_1788_; uint8_t v___x_1789_; 
v___x_1788_ = lean_ptr_addr(v_type_1738_);
v___x_1789_ = lean_usize_dec_eq(v___x_1788_, v___x_1788_);
if (v___x_1789_ == 0)
{
v___y_1747_ = v___x_1789_;
goto v___jp_1746_;
}
else
{
size_t v___x_1790_; size_t v___x_1791_; uint8_t v___x_1792_; 
v___x_1790_ = lean_ptr_addr(v_value_1739_);
v___x_1791_ = lean_ptr_addr(v_val_1743_);
v___x_1792_ = lean_usize_dec_eq(v___x_1790_, v___x_1791_);
v___y_1747_ = v___x_1792_;
goto v___jp_1746_;
}
}
v___jp_1746_:
{
if (v___y_1747_ == 0)
{
lean_object* v___x_1748_; 
lean_inc_ref(v_body_1740_);
lean_inc_ref(v_type_1738_);
lean_inc(v_declName_1737_);
lean_dec_ref(v_e_1731_);
v___x_1748_ = l_Lean_Expr_letE___override(v_declName_1737_, v_type_1738_, v_val_1743_, v_body_1740_, v_nondep_1741_);
v_e_1731_ = v___x_1748_;
goto _start;
}
else
{
size_t v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = lean_ptr_addr(v_body_1740_);
v___x_1751_ = lean_usize_dec_eq(v___x_1750_, v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; 
lean_inc_ref(v_body_1740_);
lean_inc_ref(v_type_1738_);
lean_inc(v_declName_1737_);
lean_dec_ref(v_e_1731_);
v___x_1752_ = l_Lean_Expr_letE___override(v_declName_1737_, v_type_1738_, v_val_1743_, v_body_1740_, v_nondep_1741_);
v_e_1731_ = v___x_1752_;
goto _start;
}
else
{
lean_dec(v_val_1743_);
goto _start;
}
}
}
}
else
{
lean_object* v_a_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
lean_dec(v_val_1743_);
lean_dec_ref(v_e_1731_);
v_a_1793_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1800_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1795_ = v___x_1744_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_a_1793_);
lean_dec(v___x_1744_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_a_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
else
{
lean_object* v___x_1801_; lean_object* v_num_1802_; uint8_t v___x_1803_; 
lean_dec(v___x_1742_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v_num_1802_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_numLetsWithValueNotIsWfParam(v_e_1731_, v___x_1801_);
v___x_1803_ = lean_nat_dec_lt(v___x_1801_, v_num_1802_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec(v_num_1802_);
lean_dec_ref(v_e_1731_);
v___x_1804_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4, &l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___closed__4);
v___x_1805_ = l_panic___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__0(v___x_1804_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
return v___x_1805_;
}
else
{
lean_object* v___f_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; 
v___f_1806_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0___boxed), 7, 0);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_num_1802_);
v___x_1808_ = 0;
v___x_1809_ = l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg(v_e_1731_, v___x_1807_, v___f_1806_, v___x_1808_, v___x_1803_, v___x_1808_, v_a_1732_, v_a_1733_, v_a_1734_, v_a_1735_);
lean_dec_ref(v___x_1807_);
return v___x_1809_;
}
}
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_e_1731_);
return v___x_1810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___lam__0(lean_object* v_xs_1811_, lean_object* v_b_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_b_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; uint8_t v___x_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1818_);
v___x_1820_ = 0;
v___x_1821_ = 1;
v___x_1822_ = l_Lean_Meta_mkLetFVars(v_xs_1811_, v_a_1819_, v___x_1820_, v___x_1820_, v___x_1821_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1822_;
}
else
{
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet___boxed(lean_object* v_e_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg(lean_object* v_e_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
uint8_t v___y_1837_; uint8_t v___x_1859_; 
v___x_1859_ = l_Lean_Expr_isLet(v_e_1830_);
if (v___x_1859_ == 0)
{
uint8_t v___x_1860_; 
v___x_1860_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_anyLetValueIsWfParam(v_e_1830_);
v___y_1837_ = v___x_1860_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___x_1859_;
goto v___jp_1836_;
}
v___jp_1836_:
{
if (v___y_1837_ == 0)
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
lean_dec_ref(v_e_1830_);
v___x_1838_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; 
v___x_1840_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet(v_e_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1850_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1850_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1841_);
v___x_1846_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1846_);
v___x_1848_ = v___x_1843_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_a_1851_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1840_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1840_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___redArg___boxed(lean_object* v_e_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet(lean_object* v_e_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_Elab_WF_paramLet___redArg(v_e_1868_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___boxed(lean_object* v_e_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_Elab_WF_paramLet(v_e_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_(){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1896_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_1897_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1898_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_1895_, v___x_1896_, v___x_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12____boxed(lean_object* v_a_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
return v_res_1900_;
}
}
static lean_object* _init_l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_paramLet___boxed), 9, 0);
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_(){
_start:
{
lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_1905_ = 1;
v___x_1906_ = lean_obj_once(&l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_, &l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14__once, _init_l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_);
v___x_1907_ = l_Lean_Meta_Simp_addSimprocBuiltinAttr(v___x_1904_, v___x_1905_, v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14____boxed(lean_object* v_a_1908_){
_start:
{
lean_object* v_res_1909_; 
v_res_1909_ = l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(lean_object* v_lctx_1910_, lean_object* v_x_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v_keyedConfig_1917_; uint8_t v_trackZetaDelta_1918_; lean_object* v_zetaDeltaSet_1919_; lean_object* v_localInstances_1920_; lean_object* v_defEqCtx_x3f_1921_; lean_object* v_synthPendingDepth_1922_; lean_object* v_canUnfold_x3f_1923_; uint8_t v_univApprox_1924_; uint8_t v_inTypeClassResolution_1925_; uint8_t v_cacheInferType_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_keyedConfig_1917_ = lean_ctor_get(v___y_1912_, 0);
v_trackZetaDelta_1918_ = lean_ctor_get_uint8(v___y_1912_, sizeof(void*)*7);
v_zetaDeltaSet_1919_ = lean_ctor_get(v___y_1912_, 1);
v_localInstances_1920_ = lean_ctor_get(v___y_1912_, 3);
v_defEqCtx_x3f_1921_ = lean_ctor_get(v___y_1912_, 4);
v_synthPendingDepth_1922_ = lean_ctor_get(v___y_1912_, 5);
v_canUnfold_x3f_1923_ = lean_ctor_get(v___y_1912_, 6);
v_univApprox_1924_ = lean_ctor_get_uint8(v___y_1912_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1925_ = lean_ctor_get_uint8(v___y_1912_, sizeof(void*)*7 + 2);
v_cacheInferType_1926_ = lean_ctor_get_uint8(v___y_1912_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1923_);
lean_inc(v_synthPendingDepth_1922_);
lean_inc(v_defEqCtx_x3f_1921_);
lean_inc_ref(v_localInstances_1920_);
lean_inc(v_zetaDeltaSet_1919_);
lean_inc_ref(v_keyedConfig_1917_);
v___x_1927_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1927_, 0, v_keyedConfig_1917_);
lean_ctor_set(v___x_1927_, 1, v_zetaDeltaSet_1919_);
lean_ctor_set(v___x_1927_, 2, v_lctx_1910_);
lean_ctor_set(v___x_1927_, 3, v_localInstances_1920_);
lean_ctor_set(v___x_1927_, 4, v_defEqCtx_x3f_1921_);
lean_ctor_set(v___x_1927_, 5, v_synthPendingDepth_1922_);
lean_ctor_set(v___x_1927_, 6, v_canUnfold_x3f_1923_);
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*7, v_trackZetaDelta_1918_);
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*7 + 1, v_univApprox_1924_);
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1925_);
lean_ctor_set_uint8(v___x_1927_, sizeof(void*)*7 + 3, v_cacheInferType_1926_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1913_);
v___x_1928_ = lean_apply_5(v_x_1911_, v___x_1927_, v___y_1913_, v___y_1914_, v___y_1915_, lean_box(0));
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg___boxed(lean_object* v_lctx_1929_, lean_object* v_x_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1929_, v_x_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(lean_object* v_00_u03b1_1937_, lean_object* v_lctx_1938_, lean_object* v_x_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_lctx_1938_, v_x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___boxed(lean_object* v_00_u03b1_1946_, lean_object* v_lctx_1947_, lean_object* v_x_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0(v_00_u03b1_1946_, v_lctx_1947_, v_x_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(lean_object* v_e_1955_, lean_object* v_k_1956_, uint8_t v_cleanupAnnotations_1957_, uint8_t v_preserveNondepLet_1958_, uint8_t v_nondepLetOnly_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___f_1965_; uint8_t v___x_1966_; uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1965_, 0, v_k_1956_);
v___x_1966_ = 0;
v___x_1967_ = 1;
v___x_1968_ = lean_box(0);
v___x_1969_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_1955_, v___x_1966_, v___x_1967_, v_preserveNondepLet_1958_, v_nondepLetOnly_1959_, v___x_1968_, v___f_1965_, v_cleanupAnnotations_1957_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
else
{
lean_object* v_a_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1985_; 
v_a_1978_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1985_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1985_ == 0)
{
v___x_1980_ = v___x_1969_;
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_a_1978_);
lean_dec(v___x_1969_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1985_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_a_1978_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg___boxed(lean_object* v_e_1986_, lean_object* v_k_1987_, lean_object* v_cleanupAnnotations_1988_, lean_object* v_preserveNondepLet_1989_, lean_object* v_nondepLetOnly_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1996_; uint8_t v_preserveNondepLet_boxed_1997_; uint8_t v_nondepLetOnly_boxed_1998_; lean_object* v_res_1999_; 
v_cleanupAnnotations_boxed_1996_ = lean_unbox(v_cleanupAnnotations_1988_);
v_preserveNondepLet_boxed_1997_ = lean_unbox(v_preserveNondepLet_1989_);
v_nondepLetOnly_boxed_1998_ = lean_unbox(v_nondepLetOnly_1990_);
v_res_1999_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_1986_, v_k_1987_, v_cleanupAnnotations_boxed_1996_, v_preserveNondepLet_boxed_1997_, v_nondepLetOnly_boxed_1998_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(lean_object* v_00_u03b1_2000_, lean_object* v_e_2001_, lean_object* v_k_2002_, uint8_t v_cleanupAnnotations_2003_, uint8_t v_preserveNondepLet_2004_, uint8_t v_nondepLetOnly_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2001_, v_k_2002_, v_cleanupAnnotations_2003_, v_preserveNondepLet_2004_, v_nondepLetOnly_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_e_2013_, lean_object* v_k_2014_, lean_object* v_cleanupAnnotations_2015_, lean_object* v_preserveNondepLet_2016_, lean_object* v_nondepLetOnly_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2023_; uint8_t v_preserveNondepLet_boxed_2024_; uint8_t v_nondepLetOnly_boxed_2025_; lean_object* v_res_2026_; 
v_cleanupAnnotations_boxed_2023_ = lean_unbox(v_cleanupAnnotations_2015_);
v_preserveNondepLet_boxed_2024_ = lean_unbox(v_preserveNondepLet_2016_);
v_nondepLetOnly_boxed_2025_ = lean_unbox(v_nondepLetOnly_2017_);
v_res_2026_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2(v_00_u03b1_2012_, v_e_2013_, v_k_2014_, v_cleanupAnnotations_boxed_2023_, v_preserveNondepLet_boxed_2024_, v_nondepLetOnly_boxed_2025_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
lean_dec(v___y_2021_);
lean_dec_ref(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(lean_object* v_e_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_e_2027_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0___boxed(lean_object* v_e_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__0(v_e_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(lean_object* v_as_2042_, size_t v_i_2043_, size_t v_stop_2044_, lean_object* v_b_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_eq(v_i_2043_, v_stop_2044_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2052_ = lean_array_uget_borrowed(v_as_2042_, v_i_2043_);
v___x_2053_ = l_Lean_Expr_fvarId_x21(v___x_2052_);
v___x_2054_ = l_Lean_FVarId_getDecl___redArg(v___x_2053_, v___y_2046_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; uint8_t v_a_2057_; uint8_t v___x_2063_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___x_2054_);
v___x_2063_ = l_Lean_LocalDecl_isNondep(v_a_2055_);
if (v___x_2063_ == 0)
{
v_a_2057_ = v___x_2063_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = l_Lean_LocalDecl_type(v_a_2055_);
v___x_2065_ = l_Lean_Meta_isProp(v___x_2064_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; uint8_t v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = lean_unbox(v_a_2066_);
lean_dec(v_a_2066_);
v_a_2057_ = v___x_2067_;
goto v___jp_2056_;
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2055_);
lean_dec_ref(v_b_2045_);
v_a_2068_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2065_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2065_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
v___jp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; size_t v___x_2060_; size_t v___x_2061_; 
v___x_2058_ = l_Lean_LocalDecl_setNondep(v_a_2055_, v_a_2057_);
v___x_2059_ = l_Lean_LocalContext_addDecl(v_b_2045_, v___x_2058_);
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2043_, v___x_2060_);
v_i_2043_ = v___x_2061_;
v_b_2045_ = v___x_2059_;
goto _start;
}
}
else
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref(v_b_2045_);
v_a_2076_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2078_ = v___x_2054_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2054_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_a_2076_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2084_, 0, v_b_2045_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1___boxed(lean_object* v_as_2085_, lean_object* v_i_2086_, lean_object* v_stop_2087_, lean_object* v_b_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
size_t v_i_boxed_2094_; size_t v_stop_boxed_2095_; lean_object* v_res_2096_; 
v_i_boxed_2094_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_stop_boxed_2095_ = lean_unbox_usize(v_stop_2087_);
lean_dec(v_stop_2087_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_as_2085_, v_i_boxed_2094_, v_stop_boxed_2095_, v_b_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec_ref(v_as_2085_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(uint8_t v_a_2097_, lean_object* v_lctx_2098_, lean_object* v_xs_2099_, lean_object* v_b_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_a_2107_; lean_object* v___y_2115_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = lean_array_get_size(v_xs_2099_);
v___x_2127_ = lean_nat_dec_lt(v___x_2125_, v___x_2126_);
if (v___x_2127_ == 0)
{
v_a_2107_ = v_lctx_2098_;
goto v___jp_2106_;
}
else
{
uint8_t v___x_2128_; 
v___x_2128_ = lean_nat_dec_le(v___x_2126_, v___x_2126_);
if (v___x_2128_ == 0)
{
if (v___x_2127_ == 0)
{
v_a_2107_ = v_lctx_2098_;
goto v___jp_2106_;
}
else
{
size_t v___x_2129_; size_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = ((size_t)0ULL);
v___x_2130_ = lean_usize_of_nat(v___x_2126_);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2099_, v___x_2129_, v___x_2130_, v_lctx_2098_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
v___y_2115_ = v___x_2131_;
goto v___jp_2114_;
}
}
else
{
size_t v___x_2132_; size_t v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = lean_usize_of_nat(v___x_2126_);
v___x_2134_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__1(v_xs_2099_, v___x_2132_, v___x_2133_, v_lctx_2098_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
v___y_2115_ = v___x_2134_;
goto v___jp_2114_;
}
}
v___jp_2106_:
{
uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2108_ = 1;
v___x_2109_ = lean_box(v_a_2097_);
v___x_2110_ = lean_box(v_a_2097_);
v___x_2111_ = lean_box(v___x_2108_);
v___x_2112_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_2112_, 0, v_xs_2099_);
lean_closure_set(v___x_2112_, 1, v_b_2100_);
lean_closure_set(v___x_2112_, 2, v___x_2109_);
lean_closure_set(v___x_2112_, 3, v___x_2110_);
lean_closure_set(v___x_2112_, 4, v___x_2111_);
v___x_2113_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__0___redArg(v_a_2107_, v___x_2112_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
return v___x_2113_;
}
v___jp_2114_:
{
if (lean_obj_tag(v___y_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___y_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___y_2115_);
v_a_2107_ = v_a_2116_;
goto v___jp_2106_;
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec_ref(v_b_2100_);
lean_dec_ref(v_xs_2099_);
v_a_2117_ = lean_ctor_get(v___y_2115_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___y_2115_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___y_2115_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___y_2115_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed(lean_object* v_a_2135_, lean_object* v_lctx_2136_, lean_object* v_xs_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
uint8_t v_a_11012__boxed_2144_; lean_object* v_res_2145_; 
v_a_11012__boxed_2144_ = lean_unbox(v_a_2135_);
v_res_2145_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_11012__boxed_2144_, v_lctx_2136_, v_xs_2137_, v_b_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(lean_object* v_e_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
lean_inc_ref(v_e_2146_);
v___x_2152_ = l_Lean_Meta_isProof(v_e_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2190_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2190_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2190_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
uint8_t v___x_2157_; 
v___x_2157_ = lean_unbox(v_a_2153_);
if (v___x_2157_ == 0)
{
uint8_t v___x_2158_; 
v___x_2158_ = l_Lean_Expr_isLet(v_e_2146_);
if (v___x_2158_ == 0)
{
lean_object* v___x_2159_; lean_object* v___x_2161_; 
lean_dec(v_a_2153_);
lean_dec_ref(v_e_2146_);
v___x_2159_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2159_);
v___x_2161_ = v___x_2155_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
else
{
lean_object* v_lctx_2163_; lean_object* v___f_2164_; uint8_t v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; 
lean_del_object(v___x_2155_);
v_lctx_2163_ = lean_ctor_get(v___y_2147_, 2);
lean_inc_ref(v_lctx_2163_);
lean_inc(v_a_2153_);
v___f_2164_ = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1___boxed), 9, 2);
lean_closure_set(v___f_2164_, 0, v_a_2153_);
lean_closure_set(v___f_2164_, 1, v_lctx_2163_);
v___x_2165_ = lean_unbox(v_a_2153_);
v___x_2166_ = lean_unbox(v_a_2153_);
lean_dec(v_a_2153_);
v___x_2167_ = l_Lean_Meta_letTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__2___redArg(v_e_2146_, v___f_2164_, v___x_2165_, v___x_2158_, v___x_2166_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2177_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2177_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2177_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2175_; 
v___x_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2168_);
v___x_2173_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2173_);
v___x_2175_ = v___x_2170_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
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
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
v_a_2178_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2167_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2167_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2188_; 
lean_dec(v_a_2153_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_e_2146_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 0, v___x_2186_);
v___x_2188_ = v___x_2155_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2186_);
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
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v_e_2146_);
v_a_2191_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2152_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2152_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2___boxed(lean_object* v_e_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__2(v_e_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_object* v_00_u03b1_2206_, lean_object* v_x_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = lean_apply_1(v_x_2207_, lean_box(0));
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2215_, lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(v_00_u03b1_2215_, v_x_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2222_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = l_Lean_maxRecDepthErrorMessage;
v___x_2229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__3);
v___x_2231_ = l_Lean_MessageData_ofFormat(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__4);
v___x_2233_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__2));
v___x_2234_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
lean_ctor_set(v___x_2234_, 1, v___x_2232_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(lean_object* v_ref_2235_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v_ref_2235_);
lean_ctor_set(v___x_2238_, 1, v___x_2237_);
v___x_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___boxed(lean_object* v_ref_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2240_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(lean_object* v_x_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___y_2251_; lean_object* v_fileName_2260_; lean_object* v_fileMap_2261_; lean_object* v_options_2262_; lean_object* v_currRecDepth_2263_; lean_object* v_maxRecDepth_2264_; lean_object* v_ref_2265_; lean_object* v_currNamespace_2266_; lean_object* v_openDecls_2267_; lean_object* v_initHeartbeats_2268_; lean_object* v_maxHeartbeats_2269_; lean_object* v_quotContext_2270_; lean_object* v_currMacroScope_2271_; uint8_t v_diag_2272_; lean_object* v_cancelTk_x3f_2273_; uint8_t v_suppressElabErrors_2274_; lean_object* v_inheritedTraceOptions_2275_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_fileName_2260_ = lean_ctor_get(v___y_2247_, 0);
v_fileMap_2261_ = lean_ctor_get(v___y_2247_, 1);
v_options_2262_ = lean_ctor_get(v___y_2247_, 2);
v_currRecDepth_2263_ = lean_ctor_get(v___y_2247_, 3);
v_maxRecDepth_2264_ = lean_ctor_get(v___y_2247_, 4);
v_ref_2265_ = lean_ctor_get(v___y_2247_, 5);
v_currNamespace_2266_ = lean_ctor_get(v___y_2247_, 6);
v_openDecls_2267_ = lean_ctor_get(v___y_2247_, 7);
v_initHeartbeats_2268_ = lean_ctor_get(v___y_2247_, 8);
v_maxHeartbeats_2269_ = lean_ctor_get(v___y_2247_, 9);
v_quotContext_2270_ = lean_ctor_get(v___y_2247_, 10);
v_currMacroScope_2271_ = lean_ctor_get(v___y_2247_, 11);
v_diag_2272_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*14);
v_cancelTk_x3f_2273_ = lean_ctor_get(v___y_2247_, 12);
v_suppressElabErrors_2274_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2275_ = lean_ctor_get(v___y_2247_, 13);
v___x_2281_ = lean_unsigned_to_nat(0u);
v___x_2282_ = lean_nat_dec_eq(v_maxRecDepth_2264_, v___x_2281_);
if (v___x_2282_ == 0)
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_nat_dec_eq(v_currRecDepth_2263_, v_maxRecDepth_2264_);
if (v___x_2283_ == 0)
{
goto v___jp_2276_;
}
else
{
lean_object* v___x_2284_; 
lean_dec_ref(v_x_2243_);
lean_inc(v_ref_2265_);
v___x_2284_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2265_);
v___y_2251_ = v___x_2284_;
goto v___jp_2250_;
}
}
else
{
goto v___jp_2276_;
}
v___jp_2250_:
{
if (lean_obj_tag(v___y_2251_) == 0)
{
return v___y_2251_;
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
v_a_2252_ = lean_ctor_get(v___y_2251_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___y_2251_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___y_2251_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___y_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
v___jp_2276_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2277_ = lean_unsigned_to_nat(1u);
v___x_2278_ = lean_nat_add(v_currRecDepth_2263_, v___x_2277_);
lean_inc_ref(v_inheritedTraceOptions_2275_);
lean_inc(v_cancelTk_x3f_2273_);
lean_inc(v_currMacroScope_2271_);
lean_inc(v_quotContext_2270_);
lean_inc(v_maxHeartbeats_2269_);
lean_inc(v_initHeartbeats_2268_);
lean_inc(v_openDecls_2267_);
lean_inc(v_currNamespace_2266_);
lean_inc(v_ref_2265_);
lean_inc(v_maxRecDepth_2264_);
lean_inc_ref(v_options_2262_);
lean_inc_ref(v_fileMap_2261_);
lean_inc_ref(v_fileName_2260_);
v___x_2279_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2279_, 0, v_fileName_2260_);
lean_ctor_set(v___x_2279_, 1, v_fileMap_2261_);
lean_ctor_set(v___x_2279_, 2, v_options_2262_);
lean_ctor_set(v___x_2279_, 3, v___x_2278_);
lean_ctor_set(v___x_2279_, 4, v_maxRecDepth_2264_);
lean_ctor_set(v___x_2279_, 5, v_ref_2265_);
lean_ctor_set(v___x_2279_, 6, v_currNamespace_2266_);
lean_ctor_set(v___x_2279_, 7, v_openDecls_2267_);
lean_ctor_set(v___x_2279_, 8, v_initHeartbeats_2268_);
lean_ctor_set(v___x_2279_, 9, v_maxHeartbeats_2269_);
lean_ctor_set(v___x_2279_, 10, v_quotContext_2270_);
lean_ctor_set(v___x_2279_, 11, v_currMacroScope_2271_);
lean_ctor_set(v___x_2279_, 12, v_cancelTk_x3f_2273_);
lean_ctor_set(v___x_2279_, 13, v_inheritedTraceOptions_2275_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*14, v_diag_2272_);
lean_ctor_set_uint8(v___x_2279_, sizeof(void*)*14 + 1, v_suppressElabErrors_2274_);
lean_inc(v___y_2248_);
lean_inc(v___y_2246_);
lean_inc_ref(v___y_2245_);
lean_inc(v___y_2244_);
v___x_2280_ = lean_apply_6(v_x_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___x_2279_, v___y_2248_, lean_box(0));
v___y_2251_ = v___x_2280_;
goto v___jp_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object* v_a_2293_, lean_object* v_x_2294_){
_start:
{
if (lean_obj_tag(v_x_2294_) == 0)
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_box(0);
return v___x_2295_;
}
else
{
lean_object* v_key_2296_; lean_object* v_value_2297_; lean_object* v_tail_2298_; uint8_t v___x_2299_; 
v_key_2296_ = lean_ctor_get(v_x_2294_, 0);
v_value_2297_ = lean_ctor_get(v_x_2294_, 1);
v_tail_2298_ = lean_ctor_get(v_x_2294_, 2);
v___x_2299_ = l_Lean_ExprStructEq_beq(v_key_2296_, v_a_2293_);
if (v___x_2299_ == 0)
{
v_x_2294_ = v_tail_2298_;
goto _start;
}
else
{
lean_object* v___x_2301_; 
lean_inc(v_value_2297_);
v___x_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2301_, 0, v_value_2297_);
return v___x_2301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_a_2302_, lean_object* v_x_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2302_, v_x_2303_);
lean_dec(v_x_2303_);
lean_dec_ref(v_a_2302_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_m_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v_buckets_2307_; lean_object* v___x_2308_; uint64_t v___x_2309_; uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v_fold_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; size_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_buckets_2307_ = lean_ctor_get(v_m_2305_, 1);
v___x_2308_ = lean_array_get_size(v_buckets_2307_);
v___x_2309_ = l_Lean_ExprStructEq_hash(v_a_2306_);
v___x_2310_ = 32ULL;
v___x_2311_ = lean_uint64_shift_right(v___x_2309_, v___x_2310_);
v_fold_2312_ = lean_uint64_xor(v___x_2309_, v___x_2311_);
v___x_2313_ = 16ULL;
v___x_2314_ = lean_uint64_shift_right(v_fold_2312_, v___x_2313_);
v___x_2315_ = lean_uint64_xor(v_fold_2312_, v___x_2314_);
v___x_2316_ = lean_uint64_to_usize(v___x_2315_);
v___x_2317_ = lean_usize_of_nat(v___x_2308_);
v___x_2318_ = ((size_t)1ULL);
v___x_2319_ = lean_usize_sub(v___x_2317_, v___x_2318_);
v___x_2320_ = lean_usize_land(v___x_2316_, v___x_2319_);
v___x_2321_ = lean_array_uget_borrowed(v_buckets_2307_, v___x_2320_);
v___x_2322_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2306_, v___x_2321_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_m_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_2323_, v_a_2324_);
lean_dec_ref(v_a_2324_);
lean_dec_ref(v_m_2323_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2326_, lean_object* v___y_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; 
lean_inc(v___y_2332_);
lean_inc_ref(v___y_2331_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v___y_2327_);
v___x_2334_ = lean_apply_7(v_k_2326_, v_b_2328_, v___y_2327_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, lean_box(0));
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2335_, lean_object* v___y_2336_, lean_object* v_b_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2335_, v___y_2336_, v_b_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2336_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2344_, uint8_t v_bi_2345_, lean_object* v_type_2346_, lean_object* v_k_2347_, uint8_t v_kind_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___f_2355_; lean_object* v___x_2356_; 
lean_inc(v___y_2349_);
v___f_2355_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2355_, 0, v_k_2347_);
lean_closure_set(v___f_2355_, 1, v___y_2349_);
v___x_2356_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2344_, v_bi_2345_, v_type_2346_, v___f_2355_, v_kind_2348_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
if (lean_obj_tag(v___x_2356_) == 0)
{
return v___x_2356_;
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2365_, lean_object* v_bi_2366_, lean_object* v_type_2367_, lean_object* v_k_2368_, lean_object* v_kind_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v_bi_boxed_2376_; uint8_t v_kind_boxed_2377_; lean_object* v_res_2378_; 
v_bi_boxed_2376_ = lean_unbox(v_bi_2366_);
v_kind_boxed_2377_ = lean_unbox(v_kind_2369_);
v_res_2378_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2365_, v_bi_boxed_2376_, v_type_2367_, v_k_2368_, v_kind_boxed_2377_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object* v___x_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2379_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2393_, lean_object* v_type_2394_, lean_object* v_val_2395_, lean_object* v_k_2396_, uint8_t v_nondep_2397_, uint8_t v_kind_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___f_2405_; lean_object* v___x_2406_; 
lean_inc(v___y_2399_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2405_, 0, v_k_2396_);
lean_closure_set(v___f_2405_, 1, v___y_2399_);
v___x_2406_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2393_, v_type_2394_, v_val_2395_, v___f_2405_, v_nondep_2397_, v_kind_2398_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
if (lean_obj_tag(v___x_2406_) == 0)
{
return v___x_2406_;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2406_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2406_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2415_, lean_object* v_type_2416_, lean_object* v_val_2417_, lean_object* v_k_2418_, lean_object* v_nondep_2419_, lean_object* v_kind_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
uint8_t v_nondep_boxed_2427_; uint8_t v_kind_boxed_2428_; lean_object* v_res_2429_; 
v_nondep_boxed_2427_ = lean_unbox(v_nondep_2419_);
v_kind_boxed_2428_ = lean_unbox(v_kind_2420_);
v_res_2429_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2415_, v_type_2416_, v_val_2417_, v_k_2418_, v_nondep_boxed_2427_, v_kind_boxed_2428_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2430_, lean_object* v_x_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_apply_1(v_x_2431_, lean_box(0));
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2439_, lean_object* v_x_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2439_, v_x_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
return v_res_2446_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2447_, lean_object* v_x_2448_){
_start:
{
if (lean_obj_tag(v_x_2448_) == 0)
{
uint8_t v___x_2449_; 
v___x_2449_ = 0;
return v___x_2449_;
}
else
{
lean_object* v_key_2450_; lean_object* v_tail_2451_; uint8_t v___x_2452_; 
v_key_2450_ = lean_ctor_get(v_x_2448_, 0);
v_tail_2451_ = lean_ctor_get(v_x_2448_, 2);
v___x_2452_ = l_Lean_ExprStructEq_beq(v_key_2450_, v_a_2447_);
if (v___x_2452_ == 0)
{
v_x_2448_ = v_tail_2451_;
goto _start;
}
else
{
return v___x_2452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2454_, lean_object* v_x_2455_){
_start:
{
uint8_t v_res_2456_; lean_object* v_r_2457_; 
v_res_2456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2454_, v_x_2455_);
lean_dec(v_x_2455_);
lean_dec_ref(v_a_2454_);
v_r_2457_ = lean_box(v_res_2456_);
return v_r_2457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2458_, lean_object* v_b_2459_, lean_object* v_x_2460_){
_start:
{
if (lean_obj_tag(v_x_2460_) == 0)
{
lean_dec(v_b_2459_);
lean_dec_ref(v_a_2458_);
return v_x_2460_;
}
else
{
lean_object* v_key_2461_; lean_object* v_value_2462_; lean_object* v_tail_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2475_; 
v_key_2461_ = lean_ctor_get(v_x_2460_, 0);
v_value_2462_ = lean_ctor_get(v_x_2460_, 1);
v_tail_2463_ = lean_ctor_get(v_x_2460_, 2);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_x_2460_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2465_ = v_x_2460_;
v_isShared_2466_ = v_isSharedCheck_2475_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_tail_2463_);
lean_inc(v_value_2462_);
lean_inc(v_key_2461_);
lean_dec(v_x_2460_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2475_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
uint8_t v___x_2467_; 
v___x_2467_ = l_Lean_ExprStructEq_beq(v_key_2461_, v_a_2458_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2468_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2458_, v_b_2459_, v_tail_2463_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 2, v___x_2468_);
v___x_2470_ = v___x_2465_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_key_2461_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_value_2462_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
lean_object* v___x_2473_; 
lean_dec(v_value_2462_);
lean_dec(v_key_2461_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 1, v_b_2459_);
lean_ctor_set(v___x_2465_, 0, v_a_2458_);
v___x_2473_ = v___x_2465_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2458_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_b_2459_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_tail_2463_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2476_, lean_object* v_x_2477_){
_start:
{
if (lean_obj_tag(v_x_2477_) == 0)
{
return v_x_2476_;
}
else
{
lean_object* v_key_2478_; lean_object* v_value_2479_; lean_object* v_tail_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2503_; 
v_key_2478_ = lean_ctor_get(v_x_2477_, 0);
v_value_2479_ = lean_ctor_get(v_x_2477_, 1);
v_tail_2480_ = lean_ctor_get(v_x_2477_, 2);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_x_2477_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2482_ = v_x_2477_;
v_isShared_2483_ = v_isSharedCheck_2503_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_tail_2480_);
lean_inc(v_value_2479_);
lean_inc(v_key_2478_);
lean_dec(v_x_2477_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2503_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; uint64_t v___x_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v_fold_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2484_ = lean_array_get_size(v_x_2476_);
v___x_2485_ = l_Lean_ExprStructEq_hash(v_key_2478_);
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
v___x_2497_ = lean_array_uget_borrowed(v_x_2476_, v___x_2496_);
lean_inc(v___x_2497_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 2, v___x_2497_);
v___x_2499_ = v___x_2482_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_key_2478_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_value_2479_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v___x_2497_);
v___x_2499_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; 
v___x_2500_ = lean_array_uset(v_x_2476_, v___x_2496_, v___x_2499_);
v_x_2476_ = v___x_2500_;
v_x_2477_ = v_tail_2480_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2504_, lean_object* v_source_2505_, lean_object* v_target_2506_){
_start:
{
lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2507_ = lean_array_get_size(v_source_2505_);
v___x_2508_ = lean_nat_dec_lt(v_i_2504_, v___x_2507_);
if (v___x_2508_ == 0)
{
lean_dec_ref(v_source_2505_);
lean_dec(v_i_2504_);
return v_target_2506_;
}
else
{
lean_object* v_es_2509_; lean_object* v___x_2510_; lean_object* v_source_2511_; lean_object* v_target_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_es_2509_ = lean_array_fget(v_source_2505_, v_i_2504_);
v___x_2510_ = lean_box(0);
v_source_2511_ = lean_array_fset(v_source_2505_, v_i_2504_, v___x_2510_);
v_target_2512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2506_, v_es_2509_);
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_add(v_i_2504_, v___x_2513_);
lean_dec(v_i_2504_);
v_i_2504_ = v___x_2514_;
v_source_2505_ = v_source_2511_;
v_target_2506_ = v_target_2512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2516_){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v_nbuckets_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2517_ = lean_array_get_size(v_data_2516_);
v___x_2518_ = lean_unsigned_to_nat(2u);
v_nbuckets_2519_ = lean_nat_mul(v___x_2517_, v___x_2518_);
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_mk_array(v_nbuckets_2519_, v___x_2521_);
v___x_2523_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2520_, v_data_2516_, v___x_2522_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2524_, lean_object* v_a_2525_, lean_object* v_b_2526_){
_start:
{
lean_object* v_size_2527_; lean_object* v_buckets_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2571_; 
v_size_2527_ = lean_ctor_get(v_m_2524_, 0);
v_buckets_2528_ = lean_ctor_get(v_m_2524_, 1);
v_isSharedCheck_2571_ = !lean_is_exclusive(v_m_2524_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2530_ = v_m_2524_;
v_isShared_2531_ = v_isSharedCheck_2571_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_buckets_2528_);
lean_inc(v_size_2527_);
lean_dec(v_m_2524_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2571_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; uint64_t v___x_2533_; uint64_t v___x_2534_; uint64_t v___x_2535_; uint64_t v_fold_2536_; uint64_t v___x_2537_; uint64_t v___x_2538_; uint64_t v___x_2539_; size_t v___x_2540_; size_t v___x_2541_; size_t v___x_2542_; size_t v___x_2543_; size_t v___x_2544_; lean_object* v_bkt_2545_; uint8_t v___x_2546_; 
v___x_2532_ = lean_array_get_size(v_buckets_2528_);
v___x_2533_ = l_Lean_ExprStructEq_hash(v_a_2525_);
v___x_2534_ = 32ULL;
v___x_2535_ = lean_uint64_shift_right(v___x_2533_, v___x_2534_);
v_fold_2536_ = lean_uint64_xor(v___x_2533_, v___x_2535_);
v___x_2537_ = 16ULL;
v___x_2538_ = lean_uint64_shift_right(v_fold_2536_, v___x_2537_);
v___x_2539_ = lean_uint64_xor(v_fold_2536_, v___x_2538_);
v___x_2540_ = lean_uint64_to_usize(v___x_2539_);
v___x_2541_ = lean_usize_of_nat(v___x_2532_);
v___x_2542_ = ((size_t)1ULL);
v___x_2543_ = lean_usize_sub(v___x_2541_, v___x_2542_);
v___x_2544_ = lean_usize_land(v___x_2540_, v___x_2543_);
v_bkt_2545_ = lean_array_uget_borrowed(v_buckets_2528_, v___x_2544_);
v___x_2546_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2525_, v_bkt_2545_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v_size_x27_2548_; lean_object* v___x_2549_; lean_object* v_buckets_x27_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2547_ = lean_unsigned_to_nat(1u);
v_size_x27_2548_ = lean_nat_add(v_size_2527_, v___x_2547_);
lean_dec(v_size_2527_);
lean_inc(v_bkt_2545_);
v___x_2549_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2549_, 0, v_a_2525_);
lean_ctor_set(v___x_2549_, 1, v_b_2526_);
lean_ctor_set(v___x_2549_, 2, v_bkt_2545_);
v_buckets_x27_2550_ = lean_array_uset(v_buckets_2528_, v___x_2544_, v___x_2549_);
v___x_2551_ = lean_unsigned_to_nat(4u);
v___x_2552_ = lean_nat_mul(v_size_x27_2548_, v___x_2551_);
v___x_2553_ = lean_unsigned_to_nat(3u);
v___x_2554_ = lean_nat_div(v___x_2552_, v___x_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_array_get_size(v_buckets_x27_2550_);
v___x_2556_ = lean_nat_dec_le(v___x_2554_, v___x_2555_);
lean_dec(v___x_2554_);
if (v___x_2556_ == 0)
{
lean_object* v_val_2557_; lean_object* v___x_2559_; 
v_val_2557_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2550_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v_val_2557_);
lean_ctor_set(v___x_2530_, 0, v_size_x27_2548_);
v___x_2559_ = v___x_2530_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_size_x27_2548_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_val_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
else
{
lean_object* v___x_2562_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v_buckets_x27_2550_);
lean_ctor_set(v___x_2530_, 0, v_size_x27_2548_);
v___x_2562_ = v___x_2530_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_size_x27_2548_);
lean_ctor_set(v_reuseFailAlloc_2563_, 1, v_buckets_x27_2550_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
else
{
lean_object* v___x_2564_; lean_object* v_buckets_x27_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2569_; 
lean_inc(v_bkt_2545_);
v___x_2564_ = lean_box(0);
v_buckets_x27_2565_ = lean_array_uset(v_buckets_2528_, v___x_2544_, v___x_2564_);
v___x_2566_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2525_, v_b_2526_, v_bkt_2545_);
v___x_2567_ = lean_array_uset(v_buckets_x27_2565_, v___x_2544_, v___x_2566_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2567_);
v___x_2569_ = v___x_2530_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_size_2527_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v___x_2567_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2572_, lean_object* v_e_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2576_ = lean_st_ref_take(v_a_2572_);
v___x_2577_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2576_, v_e_2573_, v_a_2574_);
v___x_2578_ = lean_st_ref_set(v_a_2572_, v___x_2577_);
v___x_2579_ = lean_box(0);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2580_, lean_object* v_e_2581_, lean_object* v_a_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2580_, v_e_2581_, v_a_2582_);
lean_dec(v_a_2580_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2588_, lean_object* v_pre_2589_, lean_object* v_post_2590_, uint8_t v_usedLetOnly_2591_, uint8_t v_skipConstInApp_2592_, uint8_t v_skipInstances_2593_, lean_object* v_body_2594_, lean_object* v_x_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_array_push(v_fvars_2588_, v_x_2595_);
v___x_2603_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2589_, v_post_2590_, v_usedLetOnly_2591_, v_skipConstInApp_2592_, v_skipInstances_2593_, v___x_2602_, v_body_2594_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2604_, lean_object* v_pre_2605_, lean_object* v_post_2606_, lean_object* v_usedLetOnly_2607_, lean_object* v_skipConstInApp_2608_, lean_object* v_skipInstances_2609_, lean_object* v_body_2610_, lean_object* v_x_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
uint8_t v_usedLetOnly_boxed_2618_; uint8_t v_skipConstInApp_boxed_2619_; uint8_t v_skipInstances_boxed_2620_; lean_object* v_res_2621_; 
v_usedLetOnly_boxed_2618_ = lean_unbox(v_usedLetOnly_2607_);
v_skipConstInApp_boxed_2619_ = lean_unbox(v_skipConstInApp_2608_);
v_skipInstances_boxed_2620_ = lean_unbox(v_skipInstances_2609_);
v_res_2621_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2604_, v_pre_2605_, v_post_2606_, v_usedLetOnly_boxed_2618_, v_skipConstInApp_boxed_2619_, v_skipInstances_boxed_2620_, v_body_2610_, v_x_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_);
lean_dec(v___y_2616_);
lean_dec_ref(v___y_2615_);
lean_dec(v___y_2614_);
lean_dec_ref(v___y_2613_);
lean_dec(v___y_2612_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2622_, lean_object* v_post_2623_, uint8_t v_usedLetOnly_2624_, uint8_t v_skipConstInApp_2625_, uint8_t v_skipInstances_2626_, lean_object* v_e_2627_, lean_object* v_a_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v___x_2634_; 
lean_inc_ref(v_post_2623_);
lean_inc(v___y_2632_);
lean_inc_ref(v___y_2631_);
lean_inc(v___y_2630_);
lean_inc_ref(v___y_2629_);
lean_inc_ref(v_e_2627_);
v___x_2634_ = lean_apply_6(v_post_2623_, v_e_2627_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, lean_box(0));
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2653_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2637_ = v___x_2634_;
v_isShared_2638_ = v_isSharedCheck_2653_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___x_2634_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2653_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
switch(lean_obj_tag(v_a_2635_))
{
case 0:
{
lean_object* v_e_2639_; lean_object* v___x_2641_; 
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_post_2623_);
lean_dec_ref(v_pre_2622_);
v_e_2639_ = lean_ctor_get(v_a_2635_, 0);
lean_inc_ref(v_e_2639_);
lean_dec_ref(v_a_2635_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_e_2639_);
v___x_2641_ = v___x_2637_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_e_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
case 1:
{
lean_object* v_e_2643_; lean_object* v___x_2644_; 
lean_del_object(v___x_2637_);
lean_dec_ref(v_e_2627_);
v_e_2643_ = lean_ctor_get(v_a_2635_, 0);
lean_inc_ref(v_e_2643_);
lean_dec_ref(v_a_2635_);
v___x_2644_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2622_, v_post_2623_, v_usedLetOnly_2624_, v_skipConstInApp_2625_, v_skipInstances_2626_, v_e_2643_, v_a_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
return v___x_2644_;
}
default: 
{
lean_object* v_e_x3f_2645_; 
lean_dec_ref(v_post_2623_);
lean_dec_ref(v_pre_2622_);
v_e_x3f_2645_ = lean_ctor_get(v_a_2635_, 0);
lean_inc(v_e_x3f_2645_);
lean_dec_ref(v_a_2635_);
if (lean_obj_tag(v_e_x3f_2645_) == 0)
{
lean_object* v___x_2647_; 
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_e_2627_);
v___x_2647_ = v___x_2637_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_e_2627_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
else
{
lean_object* v_val_2649_; lean_object* v___x_2651_; 
lean_dec_ref(v_e_2627_);
v_val_2649_ = lean_ctor_get(v_e_x3f_2645_, 0);
lean_inc(v_val_2649_);
lean_dec_ref(v_e_x3f_2645_);
if (v_isShared_2638_ == 0)
{
lean_ctor_set(v___x_2637_, 0, v_val_2649_);
v___x_2651_ = v___x_2637_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_val_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_e_2627_);
lean_dec_ref(v_post_2623_);
lean_dec_ref(v_pre_2622_);
v_a_2654_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2634_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2634_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2662_, lean_object* v_post_2663_, uint8_t v_usedLetOnly_2664_, uint8_t v_skipConstInApp_2665_, uint8_t v_skipInstances_2666_, lean_object* v_fvars_2667_, lean_object* v_e_2668_, lean_object* v_a_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_){
_start:
{
if (lean_obj_tag(v_e_2668_) == 6)
{
lean_object* v_binderName_2675_; lean_object* v_binderType_2676_; lean_object* v_body_2677_; uint8_t v_binderInfo_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v_binderName_2675_ = lean_ctor_get(v_e_2668_, 0);
lean_inc(v_binderName_2675_);
v_binderType_2676_ = lean_ctor_get(v_e_2668_, 1);
lean_inc_ref(v_binderType_2676_);
v_body_2677_ = lean_ctor_get(v_e_2668_, 2);
lean_inc_ref(v_body_2677_);
v_binderInfo_2678_ = lean_ctor_get_uint8(v_e_2668_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2668_);
v___x_2679_ = lean_expr_instantiate_rev(v_binderType_2676_, v_fvars_2667_);
lean_dec_ref(v_binderType_2676_);
lean_inc_ref(v_post_2663_);
lean_inc_ref(v_pre_2662_);
v___x_2680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2662_, v_post_2663_, v_usedLetOnly_2664_, v_skipConstInApp_2665_, v_skipInstances_2666_, v___x_2679_, v_a_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___f_2685_; uint8_t v___x_2686_; lean_object* v___x_2687_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref(v___x_2680_);
v___x_2682_ = lean_box(v_usedLetOnly_2664_);
v___x_2683_ = lean_box(v_skipConstInApp_2665_);
v___x_2684_ = lean_box(v_skipInstances_2666_);
v___f_2685_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2685_, 0, v_fvars_2667_);
lean_closure_set(v___f_2685_, 1, v_pre_2662_);
lean_closure_set(v___f_2685_, 2, v_post_2663_);
lean_closure_set(v___f_2685_, 3, v___x_2682_);
lean_closure_set(v___f_2685_, 4, v___x_2683_);
lean_closure_set(v___f_2685_, 5, v___x_2684_);
lean_closure_set(v___f_2685_, 6, v_body_2677_);
v___x_2686_ = 0;
v___x_2687_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2675_, v_binderInfo_2678_, v_a_2681_, v___f_2685_, v___x_2686_, v_a_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2687_;
}
else
{
lean_dec_ref(v_body_2677_);
lean_dec(v_binderName_2675_);
lean_dec_ref(v_fvars_2667_);
lean_dec_ref(v_post_2663_);
lean_dec_ref(v_pre_2662_);
return v___x_2680_;
}
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_expr_instantiate_rev(v_e_2668_, v_fvars_2667_);
lean_dec_ref(v_e_2668_);
lean_inc_ref(v_post_2663_);
lean_inc_ref(v_pre_2662_);
v___x_2689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2662_, v_post_2663_, v_usedLetOnly_2664_, v_skipConstInApp_2665_, v_skipInstances_2666_, v___x_2688_, v_a_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; uint8_t v___x_2691_; uint8_t v___x_2692_; uint8_t v___x_2693_; lean_object* v___x_2694_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref(v___x_2689_);
v___x_2691_ = 0;
v___x_2692_ = 1;
v___x_2693_ = 1;
v___x_2694_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2667_, v_a_2690_, v___x_2691_, v_usedLetOnly_2664_, v___x_2691_, v___x_2692_, v___x_2693_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec_ref(v_fvars_2667_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v___x_2696_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2662_, v_post_2663_, v_usedLetOnly_2664_, v_skipConstInApp_2665_, v_skipInstances_2666_, v_a_2695_, v_a_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
return v___x_2696_;
}
else
{
lean_dec_ref(v_post_2663_);
lean_dec_ref(v_pre_2662_);
return v___x_2694_;
}
}
else
{
lean_dec_ref(v_fvars_2667_);
lean_dec_ref(v_post_2663_);
lean_dec_ref(v_pre_2662_);
return v___x_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2697_, lean_object* v_pre_2698_, lean_object* v_post_2699_, uint8_t v_usedLetOnly_2700_, uint8_t v_skipConstInApp_2701_, uint8_t v_skipInstances_2702_, lean_object* v_body_2703_, lean_object* v_x_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_array_push(v_fvars_2697_, v_x_2704_);
v___x_2712_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2698_, v_post_2699_, v_usedLetOnly_2700_, v_skipConstInApp_2701_, v_skipInstances_2702_, v___x_2711_, v_body_2703_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2713_, lean_object* v_pre_2714_, lean_object* v_post_2715_, lean_object* v_usedLetOnly_2716_, lean_object* v_skipConstInApp_2717_, lean_object* v_skipInstances_2718_, lean_object* v_body_2719_, lean_object* v_x_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
uint8_t v_usedLetOnly_boxed_2727_; uint8_t v_skipConstInApp_boxed_2728_; uint8_t v_skipInstances_boxed_2729_; lean_object* v_res_2730_; 
v_usedLetOnly_boxed_2727_ = lean_unbox(v_usedLetOnly_2716_);
v_skipConstInApp_boxed_2728_ = lean_unbox(v_skipConstInApp_2717_);
v_skipInstances_boxed_2729_ = lean_unbox(v_skipInstances_2718_);
v_res_2730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2713_, v_pre_2714_, v_post_2715_, v_usedLetOnly_boxed_2727_, v_skipConstInApp_boxed_2728_, v_skipInstances_boxed_2729_, v_body_2719_, v_x_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2731_, lean_object* v_post_2732_, uint8_t v_usedLetOnly_2733_, uint8_t v_skipConstInApp_2734_, uint8_t v_skipInstances_2735_, lean_object* v_fvars_2736_, lean_object* v_e_2737_, lean_object* v_a_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
if (lean_obj_tag(v_e_2737_) == 8)
{
lean_object* v_declName_2744_; lean_object* v_type_2745_; lean_object* v_value_2746_; lean_object* v_body_2747_; uint8_t v_nondep_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_declName_2744_ = lean_ctor_get(v_e_2737_, 0);
lean_inc(v_declName_2744_);
v_type_2745_ = lean_ctor_get(v_e_2737_, 1);
lean_inc_ref(v_type_2745_);
v_value_2746_ = lean_ctor_get(v_e_2737_, 2);
lean_inc_ref(v_value_2746_);
v_body_2747_ = lean_ctor_get(v_e_2737_, 3);
lean_inc_ref(v_body_2747_);
v_nondep_2748_ = lean_ctor_get_uint8(v_e_2737_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2737_);
v___x_2749_ = lean_expr_instantiate_rev(v_type_2745_, v_fvars_2736_);
lean_dec_ref(v_type_2745_);
lean_inc_ref(v_post_2732_);
lean_inc_ref(v_pre_2731_);
v___x_2750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2731_, v_post_2732_, v_usedLetOnly_2733_, v_skipConstInApp_2734_, v_skipInstances_2735_, v___x_2749_, v_a_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = lean_expr_instantiate_rev(v_value_2746_, v_fvars_2736_);
lean_dec_ref(v_value_2746_);
lean_inc_ref(v_post_2732_);
lean_inc_ref(v_pre_2731_);
v___x_2753_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2731_, v_post_2732_, v_usedLetOnly_2733_, v_skipConstInApp_2734_, v_skipInstances_2735_, v___x_2752_, v_a_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2753_) == 0)
{
lean_object* v_a_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___f_2758_; uint8_t v___x_2759_; lean_object* v___x_2760_; 
v_a_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc(v_a_2754_);
lean_dec_ref(v___x_2753_);
v___x_2755_ = lean_box(v_usedLetOnly_2733_);
v___x_2756_ = lean_box(v_skipConstInApp_2734_);
v___x_2757_ = lean_box(v_skipInstances_2735_);
v___f_2758_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2758_, 0, v_fvars_2736_);
lean_closure_set(v___f_2758_, 1, v_pre_2731_);
lean_closure_set(v___f_2758_, 2, v_post_2732_);
lean_closure_set(v___f_2758_, 3, v___x_2755_);
lean_closure_set(v___f_2758_, 4, v___x_2756_);
lean_closure_set(v___f_2758_, 5, v___x_2757_);
lean_closure_set(v___f_2758_, 6, v_body_2747_);
v___x_2759_ = 0;
v___x_2760_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2744_, v_a_2751_, v_a_2754_, v___f_2758_, v_nondep_2748_, v___x_2759_, v_a_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2760_;
}
else
{
lean_dec(v_a_2751_);
lean_dec_ref(v_body_2747_);
lean_dec(v_declName_2744_);
lean_dec_ref(v_fvars_2736_);
lean_dec_ref(v_post_2732_);
lean_dec_ref(v_pre_2731_);
return v___x_2753_;
}
}
else
{
lean_dec_ref(v_body_2747_);
lean_dec_ref(v_value_2746_);
lean_dec(v_declName_2744_);
lean_dec_ref(v_fvars_2736_);
lean_dec_ref(v_post_2732_);
lean_dec_ref(v_pre_2731_);
return v___x_2750_;
}
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_expr_instantiate_rev(v_e_2737_, v_fvars_2736_);
lean_dec_ref(v_e_2737_);
lean_inc_ref(v_post_2732_);
lean_inc_ref(v_pre_2731_);
v___x_2762_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2731_, v_post_2732_, v_usedLetOnly_2733_, v_skipConstInApp_2734_, v_skipInstances_2735_, v___x_2761_, v_a_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; uint8_t v___x_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = 0;
v___x_2765_ = 1;
v___x_2766_ = l_Lean_Meta_mkLetFVars(v_fvars_2736_, v_a_2763_, v_usedLetOnly_2733_, v___x_2764_, v___x_2765_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
lean_dec_ref(v_fvars_2736_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref(v___x_2766_);
v___x_2768_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2731_, v_post_2732_, v_usedLetOnly_2733_, v_skipConstInApp_2734_, v_skipInstances_2735_, v_a_2767_, v_a_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2768_;
}
else
{
lean_dec_ref(v_post_2732_);
lean_dec_ref(v_pre_2731_);
return v___x_2766_;
}
}
else
{
lean_dec_ref(v_fvars_2736_);
lean_dec_ref(v_post_2732_);
lean_dec_ref(v_pre_2731_);
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_pre_2769_, lean_object* v_post_2770_, uint8_t v_usedLetOnly_2771_, uint8_t v_skipConstInApp_2772_, uint8_t v_skipInstances_2773_, size_t v_sz_2774_, size_t v_i_2775_, lean_object* v_bs_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
uint8_t v___x_2783_; 
v___x_2783_ = lean_usize_dec_lt(v_i_2775_, v_sz_2774_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_dec_ref(v_post_2770_);
lean_dec_ref(v_pre_2769_);
v___x_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_bs_2776_);
return v___x_2784_;
}
else
{
lean_object* v_v_2785_; lean_object* v___x_2786_; 
v_v_2785_ = lean_array_uget_borrowed(v_bs_2776_, v_i_2775_);
lean_inc(v_v_2785_);
lean_inc_ref(v_post_2770_);
lean_inc_ref(v_pre_2769_);
v___x_2786_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2769_, v_post_2770_, v_usedLetOnly_2771_, v_skipConstInApp_2772_, v_skipInstances_2773_, v_v_2785_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v_bs_x27_2789_; size_t v___x_2790_; size_t v___x_2791_; lean_object* v___x_2792_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref(v___x_2786_);
v___x_2788_ = lean_unsigned_to_nat(0u);
v_bs_x27_2789_ = lean_array_uset(v_bs_2776_, v_i_2775_, v___x_2788_);
v___x_2790_ = ((size_t)1ULL);
v___x_2791_ = lean_usize_add(v_i_2775_, v___x_2790_);
v___x_2792_ = lean_array_uset(v_bs_x27_2789_, v_i_2775_, v_a_2787_);
v_i_2775_ = v___x_2791_;
v_bs_2776_ = v___x_2792_;
goto _start;
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_dec_ref(v_bs_2776_);
lean_dec_ref(v_post_2770_);
lean_dec_ref(v_pre_2769_);
v_a_2794_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2786_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2786_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_2802_, lean_object* v_post_2803_, uint8_t v_usedLetOnly_2804_, uint8_t v_skipConstInApp_2805_, uint8_t v_skipInstances_2806_, lean_object* v___x_2807_, lean_object* v___y_2808_, lean_object* v_b_2809_, lean_object* v_a_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2802_, v_post_2803_, v_usedLetOnly_2804_, v_skipConstInApp_2805_, v_skipInstances_2806_, v___x_2807_, v___y_2808_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2826_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2819_ = v___x_2816_;
v_isShared_2820_ = v_isSharedCheck_2826_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2826_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2821_ = lean_array_fset(v_b_2809_, v_a_2810_, v_a_2817_);
v___x_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2822_);
v___x_2824_ = v___x_2819_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref(v_b_2809_);
v_a_2827_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2816_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2816_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_2835_, lean_object* v_post_2836_, lean_object* v_usedLetOnly_2837_, lean_object* v_skipConstInApp_2838_, lean_object* v_skipInstances_2839_, lean_object* v___x_2840_, lean_object* v___y_2841_, lean_object* v_b_2842_, lean_object* v_a_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
uint8_t v_usedLetOnly_boxed_2849_; uint8_t v_skipConstInApp_boxed_2850_; uint8_t v_skipInstances_boxed_2851_; lean_object* v_res_2852_; 
v_usedLetOnly_boxed_2849_ = lean_unbox(v_usedLetOnly_2837_);
v_skipConstInApp_boxed_2850_ = lean_unbox(v_skipConstInApp_2838_);
v_skipInstances_boxed_2851_ = lean_unbox(v_skipInstances_2839_);
v_res_2852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2835_, v_post_2836_, v_usedLetOnly_boxed_2849_, v_skipConstInApp_boxed_2850_, v_skipInstances_boxed_2851_, v___x_2840_, v___y_2841_, v_b_2842_, v_a_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
lean_dec(v_a_2843_);
lean_dec(v___y_2841_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object* v_upperBound_2853_, lean_object* v___x_2854_, lean_object* v_pre_2855_, lean_object* v_post_2856_, uint8_t v_usedLetOnly_2857_, uint8_t v_skipConstInApp_2858_, uint8_t v_skipInstances_2859_, lean_object* v_a_2860_, lean_object* v_b_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
lean_object* v___y_2869_; uint8_t v___x_2892_; 
v___x_2892_ = lean_nat_dec_lt(v_a_2860_, v_upperBound_2853_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; 
lean_dec(v_a_2860_);
lean_dec_ref(v_post_2856_);
lean_dec_ref(v_pre_2855_);
v___x_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2893_, 0, v_b_2861_);
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v___x_2894_ = lean_array_fget_borrowed(v_b_2861_, v_a_2860_);
v___x_2895_ = lean_array_get_size(v___x_2854_);
v___x_2896_ = lean_nat_dec_lt(v_a_2860_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___f_2900_; 
lean_inc(v___x_2894_);
v___x_2897_ = lean_box(v_usedLetOnly_2857_);
v___x_2898_ = lean_box(v_skipConstInApp_2858_);
v___x_2899_ = lean_box(v_skipInstances_2859_);
lean_inc(v_a_2860_);
lean_inc(v___y_2862_);
lean_inc_ref(v_post_2856_);
lean_inc_ref(v_pre_2855_);
v___f_2900_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2900_, 0, v_pre_2855_);
lean_closure_set(v___f_2900_, 1, v_post_2856_);
lean_closure_set(v___f_2900_, 2, v___x_2897_);
lean_closure_set(v___f_2900_, 3, v___x_2898_);
lean_closure_set(v___f_2900_, 4, v___x_2899_);
lean_closure_set(v___f_2900_, 5, v___x_2894_);
lean_closure_set(v___f_2900_, 6, v___y_2862_);
lean_closure_set(v___f_2900_, 7, v_b_2861_);
lean_closure_set(v___f_2900_, 8, v_a_2860_);
v___y_2869_ = v___f_2900_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2901_; uint8_t v_isInstance_2902_; 
v___x_2901_ = lean_array_fget_borrowed(v___x_2854_, v_a_2860_);
v_isInstance_2902_ = lean_ctor_get_uint8(v___x_2901_, sizeof(void*)*1 + 4);
if (v_isInstance_2902_ == 0)
{
lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___f_2906_; 
lean_inc(v___x_2894_);
v___x_2903_ = lean_box(v_usedLetOnly_2857_);
v___x_2904_ = lean_box(v_skipConstInApp_2858_);
v___x_2905_ = lean_box(v_skipInstances_2859_);
lean_inc(v_a_2860_);
lean_inc(v___y_2862_);
lean_inc_ref(v_post_2856_);
lean_inc_ref(v_pre_2855_);
v___f_2906_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2906_, 0, v_pre_2855_);
lean_closure_set(v___f_2906_, 1, v_post_2856_);
lean_closure_set(v___f_2906_, 2, v___x_2903_);
lean_closure_set(v___f_2906_, 3, v___x_2904_);
lean_closure_set(v___f_2906_, 4, v___x_2905_);
lean_closure_set(v___f_2906_, 5, v___x_2894_);
lean_closure_set(v___f_2906_, 6, v___y_2862_);
lean_closure_set(v___f_2906_, 7, v_b_2861_);
lean_closure_set(v___f_2906_, 8, v_a_2860_);
v___y_2869_ = v___f_2906_;
goto v___jp_2868_;
}
else
{
lean_object* v___x_2907_; lean_object* v___f_2908_; 
v___x_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2907_, 0, v_b_2861_);
v___f_2908_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2908_, 0, v___x_2907_);
v___y_2869_ = v___f_2908_;
goto v___jp_2868_;
}
}
}
v___jp_2868_:
{
lean_object* v___x_2870_; 
lean_inc(v___y_2866_);
lean_inc_ref(v___y_2865_);
lean_inc(v___y_2864_);
lean_inc_ref(v___y_2863_);
v___x_2870_ = lean_apply_5(v___y_2869_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, lean_box(0));
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2883_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2873_ = v___x_2870_;
v_isShared_2874_ = v_isSharedCheck_2883_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2870_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2883_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
if (lean_obj_tag(v_a_2871_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; 
lean_dec(v_a_2860_);
lean_dec_ref(v_post_2856_);
lean_dec_ref(v_pre_2855_);
v_a_2875_ = lean_ctor_get(v_a_2871_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v_a_2871_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v_a_2875_);
v___x_2877_ = v___x_2873_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_del_object(v___x_2873_);
v_a_2879_ = lean_ctor_get(v_a_2871_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v_a_2871_);
v___x_2880_ = lean_unsigned_to_nat(1u);
v___x_2881_ = lean_nat_add(v_a_2860_, v___x_2880_);
lean_dec(v_a_2860_);
v_a_2860_ = v___x_2881_;
v_b_2861_ = v_a_2879_;
goto _start;
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_a_2860_);
lean_dec_ref(v_post_2856_);
lean_dec_ref(v_pre_2855_);
v_a_2884_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2870_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2870_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2909_, lean_object* v_pre_2910_, lean_object* v_post_2911_, uint8_t v_usedLetOnly_2912_, uint8_t v_skipConstInApp_2913_, lean_object* v_x_2914_, lean_object* v_x_2915_, lean_object* v_x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
lean_object* v_f_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; 
if (lean_obj_tag(v_x_2914_) == 5)
{
lean_object* v_fn_2972_; lean_object* v_arg_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_fn_2972_ = lean_ctor_get(v_x_2914_, 0);
lean_inc_ref(v_fn_2972_);
v_arg_2973_ = lean_ctor_get(v_x_2914_, 1);
lean_inc_ref(v_arg_2973_);
lean_dec_ref(v_x_2914_);
v___x_2974_ = lean_array_set(v_x_2915_, v_x_2916_, v_arg_2973_);
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_nat_sub(v_x_2916_, v___x_2975_);
lean_dec(v_x_2916_);
v_x_2914_ = v_fn_2972_;
v_x_2915_ = v___x_2974_;
v_x_2916_ = v___x_2976_;
goto _start;
}
else
{
lean_dec(v_x_2916_);
if (v_skipConstInApp_2913_ == 0)
{
goto v___jp_2969_;
}
else
{
uint8_t v___x_2978_; 
v___x_2978_ = l_Lean_Expr_isConst(v_x_2914_);
if (v___x_2978_ == 0)
{
goto v___jp_2969_;
}
else
{
v_f_2924_ = v_x_2914_;
v___y_2925_ = v___y_2917_;
v___y_2926_ = v___y_2918_;
v___y_2927_ = v___y_2919_;
v___y_2928_ = v___y_2920_;
v___y_2929_ = v___y_2921_;
goto v___jp_2923_;
}
}
}
v___jp_2923_:
{
if (v_skipInstances_2909_ == 0)
{
size_t v_sz_2930_; size_t v___x_2931_; lean_object* v___x_2932_; 
v_sz_2930_ = lean_array_size(v_x_2915_);
v___x_2931_ = ((size_t)0ULL);
lean_inc_ref(v_post_2911_);
lean_inc_ref(v_pre_2910_);
v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2910_, v_post_2911_, v_usedLetOnly_2912_, v_skipConstInApp_2913_, v_skipInstances_2909_, v_sz_2930_, v___x_2931_, v_x_2915_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = l_Lean_mkAppN(v_f_2924_, v_a_2933_);
lean_dec(v_a_2933_);
v___x_2935_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2910_, v_post_2911_, v_usedLetOnly_2912_, v_skipConstInApp_2913_, v_skipInstances_2909_, v___x_2934_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2935_;
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec_ref(v_f_2924_);
lean_dec_ref(v_post_2911_);
lean_dec_ref(v_pre_2910_);
v_a_2936_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2932_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2932_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_array_get_size(v_x_2915_);
lean_inc_ref(v_f_2924_);
v___x_2945_ = l_Lean_Meta_getFunInfoNArgs(v_f_2924_, v___x_2944_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v_paramInfo_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v_paramInfo_2947_ = lean_ctor_get(v_a_2946_, 0);
lean_inc_ref(v_paramInfo_2947_);
lean_dec(v_a_2946_);
v___x_2948_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2911_);
lean_inc_ref(v_pre_2910_);
v___x_2949_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v___x_2944_, v_paramInfo_2947_, v_pre_2910_, v_post_2911_, v_usedLetOnly_2912_, v_skipConstInApp_2913_, v_skipInstances_2909_, v___x_2948_, v_x_2915_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v_paramInfo_2947_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref(v___x_2949_);
v___x_2951_ = l_Lean_mkAppN(v_f_2924_, v_a_2950_);
lean_dec(v_a_2950_);
v___x_2952_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2910_, v_post_2911_, v_usedLetOnly_2912_, v_skipConstInApp_2913_, v_skipInstances_2909_, v___x_2951_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2952_;
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_f_2924_);
lean_dec_ref(v_post_2911_);
lean_dec_ref(v_pre_2910_);
v_a_2953_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2949_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2949_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref(v_f_2924_);
lean_dec_ref(v_x_2915_);
lean_dec_ref(v_post_2911_);
lean_dec_ref(v_pre_2910_);
v_a_2961_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2945_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2945_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
v___jp_2969_:
{
lean_object* v___x_2970_; 
lean_inc_ref(v_post_2911_);
lean_inc_ref(v_pre_2910_);
v___x_2970_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2910_, v_post_2911_, v_usedLetOnly_2912_, v_skipConstInApp_2913_, v_skipInstances_2909_, v_x_2914_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_a_2971_; 
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_a_2971_);
lean_dec_ref(v___x_2970_);
v_f_2924_ = v_a_2971_;
v___y_2925_ = v___y_2917_;
v___y_2926_ = v___y_2918_;
v___y_2927_ = v___y_2919_;
v___y_2928_ = v___y_2920_;
v___y_2929_ = v___y_2921_;
goto v___jp_2923_;
}
else
{
lean_dec_ref(v_x_2915_);
lean_dec_ref(v_post_2911_);
lean_dec_ref(v_pre_2910_);
return v___x_2970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v___x_2979_, lean_object* v_pre_2980_, lean_object* v_e_2981_, lean_object* v_post_2982_, uint8_t v_usedLetOnly_2983_, uint8_t v_skipConstInApp_2984_, uint8_t v_skipInstances_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_Core_checkSystem(v___x_2979_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v___x_2993_; 
lean_dec_ref(v___x_2992_);
lean_inc_ref(v_pre_2980_);
lean_inc(v___y_2990_);
lean_inc_ref(v___y_2989_);
lean_inc(v___y_2988_);
lean_inc_ref(v___y_2987_);
lean_inc_ref(v_e_2981_);
v___x_2993_ = lean_apply_6(v_pre_2980_, v_e_2981_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, lean_box(0));
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3042_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_2996_ = v___x_2993_;
v_isShared_2997_ = v_isSharedCheck_3042_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2993_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3042_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___y_2999_; 
switch(lean_obj_tag(v_a_2994_))
{
case 0:
{
lean_object* v_e_3034_; lean_object* v___x_3036_; 
lean_dec_ref(v_post_2982_);
lean_dec_ref(v_e_2981_);
lean_dec_ref(v_pre_2980_);
v_e_3034_ = lean_ctor_get(v_a_2994_, 0);
lean_inc_ref(v_e_3034_);
lean_dec_ref(v_a_2994_);
if (v_isShared_2997_ == 0)
{
lean_ctor_set(v___x_2996_, 0, v_e_3034_);
v___x_3036_ = v___x_2996_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_e_3034_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
case 1:
{
lean_object* v_e_3038_; lean_object* v___x_3039_; 
lean_del_object(v___x_2996_);
lean_dec_ref(v_e_2981_);
v_e_3038_ = lean_ctor_get(v_a_2994_, 0);
lean_inc_ref(v_e_3038_);
lean_dec_ref(v_a_2994_);
v___x_3039_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v_e_3038_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3039_;
}
default: 
{
lean_object* v_e_x3f_3040_; 
lean_del_object(v___x_2996_);
v_e_x3f_3040_ = lean_ctor_get(v_a_2994_, 0);
lean_inc(v_e_x3f_3040_);
lean_dec_ref(v_a_2994_);
if (lean_obj_tag(v_e_x3f_3040_) == 0)
{
v___y_2999_ = v_e_2981_;
goto v___jp_2998_;
}
else
{
lean_object* v_val_3041_; 
lean_dec_ref(v_e_2981_);
v_val_3041_ = lean_ctor_get(v_e_x3f_3040_, 0);
lean_inc(v_val_3041_);
lean_dec_ref(v_e_x3f_3040_);
v___y_2999_ = v_val_3041_;
goto v___jp_2998_;
}
}
}
v___jp_2998_:
{
switch(lean_obj_tag(v___y_2999_))
{
case 7:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3001_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___x_3000_, v___y_2999_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3001_;
}
case 6:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3003_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___x_3002_, v___y_2999_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3003_;
}
case 8:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_3005_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___x_3004_, v___y_2999_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3005_;
}
case 5:
{
lean_object* v_dummy_3006_; lean_object* v_nargs_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_dummy_3006_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3007_ = l_Lean_Expr_getAppNumArgs(v___y_2999_);
lean_inc(v_nargs_3007_);
v___x_3008_ = lean_mk_array(v_nargs_3007_, v_dummy_3006_);
v___x_3009_ = lean_unsigned_to_nat(1u);
v___x_3010_ = lean_nat_sub(v_nargs_3007_, v___x_3009_);
lean_dec(v_nargs_3007_);
v___x_3011_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_2985_, v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v___y_2999_, v___x_3008_, v___x_3010_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3011_;
}
case 10:
{
lean_object* v_data_3012_; lean_object* v_expr_3013_; lean_object* v___x_3014_; 
v_data_3012_ = lean_ctor_get(v___y_2999_, 0);
v_expr_3013_ = lean_ctor_get(v___y_2999_, 1);
lean_inc_ref(v_expr_3013_);
lean_inc_ref(v_post_2982_);
lean_inc_ref(v_pre_2980_);
v___x_3014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v_expr_3013_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; size_t v___x_3016_; size_t v___x_3017_; uint8_t v___x_3018_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = lean_ptr_addr(v_expr_3013_);
v___x_3017_ = lean_ptr_addr(v_a_3015_);
v___x_3018_ = lean_usize_dec_eq(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; 
lean_inc(v_data_3012_);
lean_dec_ref(v___y_2999_);
v___x_3019_ = l_Lean_Expr_mdata___override(v_data_3012_, v_a_3015_);
v___x_3020_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___x_3019_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; 
lean_dec(v_a_3015_);
v___x_3021_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___y_2999_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3021_;
}
}
else
{
lean_dec_ref(v___y_2999_);
lean_dec_ref(v_post_2982_);
lean_dec_ref(v_pre_2980_);
return v___x_3014_;
}
}
case 11:
{
lean_object* v_typeName_3022_; lean_object* v_idx_3023_; lean_object* v_struct_3024_; lean_object* v___x_3025_; 
v_typeName_3022_ = lean_ctor_get(v___y_2999_, 0);
v_idx_3023_ = lean_ctor_get(v___y_2999_, 1);
v_struct_3024_ = lean_ctor_get(v___y_2999_, 2);
lean_inc_ref(v_struct_3024_);
lean_inc_ref(v_post_2982_);
lean_inc_ref(v_pre_2980_);
v___x_3025_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v_struct_3024_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; size_t v___x_3027_; size_t v___x_3028_; uint8_t v___x_3029_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = lean_ptr_addr(v_struct_3024_);
v___x_3028_ = lean_ptr_addr(v_a_3026_);
v___x_3029_ = lean_usize_dec_eq(v___x_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_inc(v_idx_3023_);
lean_inc(v_typeName_3022_);
lean_dec_ref(v___y_2999_);
v___x_3030_ = l_Lean_Expr_proj___override(v_typeName_3022_, v_idx_3023_, v_a_3026_);
v___x_3031_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___x_3030_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; 
lean_dec(v_a_3026_);
v___x_3032_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___y_2999_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3032_;
}
}
else
{
lean_dec_ref(v___y_2999_);
lean_dec_ref(v_post_2982_);
lean_dec_ref(v_pre_2980_);
return v___x_3025_;
}
}
default: 
{
lean_object* v___x_3033_; 
v___x_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2980_, v_post_2982_, v_usedLetOnly_2983_, v_skipConstInApp_2984_, v_skipInstances_2985_, v___y_2999_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_3033_;
}
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v_post_2982_);
lean_dec_ref(v_e_2981_);
lean_dec_ref(v_pre_2980_);
v_a_3043_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_2993_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2993_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
else
{
lean_object* v_a_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3058_; 
lean_dec_ref(v_post_2982_);
lean_dec_ref(v_e_2981_);
lean_dec_ref(v_pre_2980_);
v_a_3051_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3053_ = v___x_2992_;
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_a_3051_);
lean_dec(v___x_2992_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3058_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3056_; 
if (v_isShared_3054_ == 0)
{
v___x_3056_ = v___x_3053_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_a_3051_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
return v___x_3056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v___x_3059_, lean_object* v_pre_3060_, lean_object* v_e_3061_, lean_object* v_post_3062_, lean_object* v_usedLetOnly_3063_, lean_object* v_skipConstInApp_3064_, lean_object* v_skipInstances_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
uint8_t v_usedLetOnly_boxed_3072_; uint8_t v_skipConstInApp_boxed_3073_; uint8_t v_skipInstances_boxed_3074_; lean_object* v_res_3075_; 
v_usedLetOnly_boxed_3072_ = lean_unbox(v_usedLetOnly_3063_);
v_skipConstInApp_boxed_3073_ = lean_unbox(v_skipConstInApp_3064_);
v_skipInstances_boxed_3074_ = lean_unbox(v_skipInstances_3065_);
v_res_3075_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v___x_3059_, v_pre_3060_, v_e_3061_, v_post_3062_, v_usedLetOnly_boxed_3072_, v_skipConstInApp_boxed_3073_, v_skipInstances_boxed_3074_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3076_, lean_object* v_post_3077_, uint8_t v_usedLetOnly_3078_, uint8_t v_skipConstInApp_3079_, uint8_t v_skipInstances_3080_, lean_object* v_e_3081_, lean_object* v_a_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_inc(v_a_3082_);
v___x_3088_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3088_, 0, lean_box(0));
lean_closure_set(v___x_3088_, 1, lean_box(0));
lean_closure_set(v___x_3088_, 2, v_a_3082_);
v___x_3089_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3088_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3124_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3092_ = v___x_3089_;
v_isShared_3093_ = v_isSharedCheck_3124_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3089_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3124_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3090_, v_e_3081_);
lean_dec(v_a_3090_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; lean_object* v___x_3100_; 
lean_del_object(v___x_3092_);
v___x_3095_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
v___x_3096_ = lean_box(v_usedLetOnly_3078_);
v___x_3097_ = lean_box(v_skipConstInApp_3079_);
v___x_3098_ = lean_box(v_skipInstances_3080_);
lean_inc_ref(v_e_3081_);
v___f_3099_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3099_, 0, v___x_3095_);
lean_closure_set(v___f_3099_, 1, v_pre_3076_);
lean_closure_set(v___f_3099_, 2, v_e_3081_);
lean_closure_set(v___f_3099_, 3, v_post_3077_);
lean_closure_set(v___f_3099_, 4, v___x_3096_);
lean_closure_set(v___f_3099_, 5, v___x_3097_);
lean_closure_set(v___f_3099_, 6, v___x_3098_);
v___x_3100_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3099_, v_a_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_n(v_a_3101_, 2);
lean_dec_ref(v___x_3100_);
lean_inc(v_a_3082_);
v___f_3102_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3102_, 0, v_a_3082_);
lean_closure_set(v___f_3102_, 1, v_e_3081_);
lean_closure_set(v___f_3102_, 2, v_a_3101_);
v___x_3103_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3102_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3110_ == 0)
{
lean_object* v_unused_3111_; 
v_unused_3111_ = lean_ctor_get(v___x_3103_, 0);
lean_dec(v_unused_3111_);
v___x_3105_ = v___x_3103_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_dec(v___x_3103_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v_a_3101_);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3101_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec(v_a_3101_);
v_a_3112_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3103_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3103_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
else
{
lean_dec_ref(v_e_3081_);
return v___x_3100_;
}
}
else
{
lean_object* v_val_3120_; lean_object* v___x_3122_; 
lean_dec_ref(v_e_3081_);
lean_dec_ref(v_post_3077_);
lean_dec_ref(v_pre_3076_);
v_val_3120_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_val_3120_);
lean_dec_ref(v___x_3094_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v_val_3120_);
v___x_3122_ = v___x_3092_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_val_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_dec_ref(v_e_3081_);
lean_dec_ref(v_post_3077_);
lean_dec_ref(v_pre_3076_);
v_a_3125_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3089_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3089_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_3133_, lean_object* v_pre_3134_, lean_object* v_post_3135_, lean_object* v_usedLetOnly_3136_, lean_object* v_skipConstInApp_3137_, lean_object* v_skipInstances_3138_, lean_object* v_body_3139_, lean_object* v_x_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
uint8_t v_usedLetOnly_boxed_3147_; uint8_t v_skipConstInApp_boxed_3148_; uint8_t v_skipInstances_boxed_3149_; lean_object* v_res_3150_; 
v_usedLetOnly_boxed_3147_ = lean_unbox(v_usedLetOnly_3136_);
v_skipConstInApp_boxed_3148_ = lean_unbox(v_skipConstInApp_3137_);
v_skipInstances_boxed_3149_ = lean_unbox(v_skipInstances_3138_);
v_res_3150_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_3133_, v_pre_3134_, v_post_3135_, v_usedLetOnly_boxed_3147_, v_skipConstInApp_boxed_3148_, v_skipInstances_boxed_3149_, v_body_3139_, v_x_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v___y_3142_);
lean_dec(v___y_3141_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3151_, lean_object* v_post_3152_, uint8_t v_usedLetOnly_3153_, uint8_t v_skipConstInApp_3154_, uint8_t v_skipInstances_3155_, lean_object* v_fvars_3156_, lean_object* v_e_3157_, lean_object* v_a_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
if (lean_obj_tag(v_e_3157_) == 7)
{
lean_object* v_binderName_3164_; lean_object* v_binderType_3165_; lean_object* v_body_3166_; uint8_t v_binderInfo_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v_binderName_3164_ = lean_ctor_get(v_e_3157_, 0);
lean_inc(v_binderName_3164_);
v_binderType_3165_ = lean_ctor_get(v_e_3157_, 1);
lean_inc_ref(v_binderType_3165_);
v_body_3166_ = lean_ctor_get(v_e_3157_, 2);
lean_inc_ref(v_body_3166_);
v_binderInfo_3167_ = lean_ctor_get_uint8(v_e_3157_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3157_);
v___x_3168_ = lean_expr_instantiate_rev(v_binderType_3165_, v_fvars_3156_);
lean_dec_ref(v_binderType_3165_);
lean_inc_ref(v_post_3152_);
lean_inc_ref(v_pre_3151_);
v___x_3169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3151_, v_post_3152_, v_usedLetOnly_3153_, v_skipConstInApp_3154_, v_skipInstances_3155_, v___x_3168_, v_a_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___f_3174_; uint8_t v___x_3175_; lean_object* v___x_3176_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v___x_3169_);
v___x_3171_ = lean_box(v_usedLetOnly_3153_);
v___x_3172_ = lean_box(v_skipConstInApp_3154_);
v___x_3173_ = lean_box(v_skipInstances_3155_);
v___f_3174_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3174_, 0, v_fvars_3156_);
lean_closure_set(v___f_3174_, 1, v_pre_3151_);
lean_closure_set(v___f_3174_, 2, v_post_3152_);
lean_closure_set(v___f_3174_, 3, v___x_3171_);
lean_closure_set(v___f_3174_, 4, v___x_3172_);
lean_closure_set(v___f_3174_, 5, v___x_3173_);
lean_closure_set(v___f_3174_, 6, v_body_3166_);
v___x_3175_ = 0;
v___x_3176_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3164_, v_binderInfo_3167_, v_a_3170_, v___f_3174_, v___x_3175_, v_a_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3176_;
}
else
{
lean_dec_ref(v_body_3166_);
lean_dec(v_binderName_3164_);
lean_dec_ref(v_fvars_3156_);
lean_dec_ref(v_post_3152_);
lean_dec_ref(v_pre_3151_);
return v___x_3169_;
}
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_expr_instantiate_rev(v_e_3157_, v_fvars_3156_);
lean_dec_ref(v_e_3157_);
lean_inc_ref(v_post_3152_);
lean_inc_ref(v_pre_3151_);
v___x_3178_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3151_, v_post_3152_, v_usedLetOnly_3153_, v_skipConstInApp_3154_, v_skipInstances_3155_, v___x_3177_, v_a_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v_a_3179_; uint8_t v___x_3180_; uint8_t v___x_3181_; uint8_t v___x_3182_; lean_object* v___x_3183_; 
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = 0;
v___x_3181_ = 1;
v___x_3182_ = 1;
v___x_3183_ = l_Lean_Meta_mkForallFVars(v_fvars_3156_, v_a_3179_, v___x_3180_, v_usedLetOnly_3153_, v___x_3181_, v___x_3182_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec_ref(v_fvars_3156_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3183_);
v___x_3185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3151_, v_post_3152_, v_usedLetOnly_3153_, v_skipConstInApp_3154_, v_skipInstances_3155_, v_a_3184_, v_a_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v___x_3185_;
}
else
{
lean_dec_ref(v_post_3152_);
lean_dec_ref(v_pre_3151_);
return v___x_3183_;
}
}
else
{
lean_dec_ref(v_fvars_3156_);
lean_dec_ref(v_post_3152_);
lean_dec_ref(v_pre_3151_);
return v___x_3178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3186_, lean_object* v_pre_3187_, lean_object* v_post_3188_, uint8_t v_usedLetOnly_3189_, uint8_t v_skipConstInApp_3190_, uint8_t v_skipInstances_3191_, lean_object* v_body_3192_, lean_object* v_x_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = lean_array_push(v_fvars_3186_, v_x_3193_);
v___x_3201_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3187_, v_post_3188_, v_usedLetOnly_3189_, v_skipConstInApp_3190_, v_skipInstances_3191_, v___x_3200_, v_body_3192_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3202_, lean_object* v_post_3203_, lean_object* v_usedLetOnly_3204_, lean_object* v_skipConstInApp_3205_, lean_object* v_skipInstances_3206_, lean_object* v_e_3207_, lean_object* v_a_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
uint8_t v_usedLetOnly_boxed_3214_; uint8_t v_skipConstInApp_boxed_3215_; uint8_t v_skipInstances_boxed_3216_; lean_object* v_res_3217_; 
v_usedLetOnly_boxed_3214_ = lean_unbox(v_usedLetOnly_3204_);
v_skipConstInApp_boxed_3215_ = lean_unbox(v_skipConstInApp_3205_);
v_skipInstances_boxed_3216_ = lean_unbox(v_skipInstances_3206_);
v_res_3217_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3202_, v_post_3203_, v_usedLetOnly_boxed_3214_, v_skipConstInApp_boxed_3215_, v_skipInstances_boxed_3216_, v_e_3207_, v_a_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v_a_3208_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_pre_3218_, lean_object* v_post_3219_, lean_object* v_usedLetOnly_3220_, lean_object* v_skipConstInApp_3221_, lean_object* v_skipInstances_3222_, lean_object* v_sz_3223_, lean_object* v_i_3224_, lean_object* v_bs_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
uint8_t v_usedLetOnly_boxed_3232_; uint8_t v_skipConstInApp_boxed_3233_; uint8_t v_skipInstances_boxed_3234_; size_t v_sz_boxed_3235_; size_t v_i_boxed_3236_; lean_object* v_res_3237_; 
v_usedLetOnly_boxed_3232_ = lean_unbox(v_usedLetOnly_3220_);
v_skipConstInApp_boxed_3233_ = lean_unbox(v_skipConstInApp_3221_);
v_skipInstances_boxed_3234_ = lean_unbox(v_skipInstances_3222_);
v_sz_boxed_3235_ = lean_unbox_usize(v_sz_3223_);
lean_dec(v_sz_3223_);
v_i_boxed_3236_ = lean_unbox_usize(v_i_3224_);
lean_dec(v_i_3224_);
v_res_3237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_3218_, v_post_3219_, v_usedLetOnly_boxed_3232_, v_skipConstInApp_boxed_3233_, v_skipInstances_boxed_3234_, v_sz_boxed_3235_, v_i_boxed_3236_, v_bs_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3238_, lean_object* v_post_3239_, lean_object* v_usedLetOnly_3240_, lean_object* v_skipConstInApp_3241_, lean_object* v_skipInstances_3242_, lean_object* v_e_3243_, lean_object* v_a_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
uint8_t v_usedLetOnly_boxed_3250_; uint8_t v_skipConstInApp_boxed_3251_; uint8_t v_skipInstances_boxed_3252_; lean_object* v_res_3253_; 
v_usedLetOnly_boxed_3250_ = lean_unbox(v_usedLetOnly_3240_);
v_skipConstInApp_boxed_3251_ = lean_unbox(v_skipConstInApp_3241_);
v_skipInstances_boxed_3252_ = lean_unbox(v_skipInstances_3242_);
v_res_3253_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3238_, v_post_3239_, v_usedLetOnly_boxed_3250_, v_skipConstInApp_boxed_3251_, v_skipInstances_boxed_3252_, v_e_3243_, v_a_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v_a_3244_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3254_, lean_object* v_post_3255_, lean_object* v_usedLetOnly_3256_, lean_object* v_skipConstInApp_3257_, lean_object* v_skipInstances_3258_, lean_object* v_fvars_3259_, lean_object* v_e_3260_, lean_object* v_a_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
uint8_t v_usedLetOnly_boxed_3267_; uint8_t v_skipConstInApp_boxed_3268_; uint8_t v_skipInstances_boxed_3269_; lean_object* v_res_3270_; 
v_usedLetOnly_boxed_3267_ = lean_unbox(v_usedLetOnly_3256_);
v_skipConstInApp_boxed_3268_ = lean_unbox(v_skipConstInApp_3257_);
v_skipInstances_boxed_3269_ = lean_unbox(v_skipInstances_3258_);
v_res_3270_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3254_, v_post_3255_, v_usedLetOnly_boxed_3267_, v_skipConstInApp_boxed_3268_, v_skipInstances_boxed_3269_, v_fvars_3259_, v_e_3260_, v_a_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v_a_3261_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3271_, lean_object* v_post_3272_, lean_object* v_usedLetOnly_3273_, lean_object* v_skipConstInApp_3274_, lean_object* v_skipInstances_3275_, lean_object* v_fvars_3276_, lean_object* v_e_3277_, lean_object* v_a_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
uint8_t v_usedLetOnly_boxed_3284_; uint8_t v_skipConstInApp_boxed_3285_; uint8_t v_skipInstances_boxed_3286_; lean_object* v_res_3287_; 
v_usedLetOnly_boxed_3284_ = lean_unbox(v_usedLetOnly_3273_);
v_skipConstInApp_boxed_3285_ = lean_unbox(v_skipConstInApp_3274_);
v_skipInstances_boxed_3286_ = lean_unbox(v_skipInstances_3275_);
v_res_3287_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3271_, v_post_3272_, v_usedLetOnly_boxed_3284_, v_skipConstInApp_boxed_3285_, v_skipInstances_boxed_3286_, v_fvars_3276_, v_e_3277_, v_a_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
lean_dec(v_a_3278_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3288_, lean_object* v_post_3289_, lean_object* v_usedLetOnly_3290_, lean_object* v_skipConstInApp_3291_, lean_object* v_skipInstances_3292_, lean_object* v_fvars_3293_, lean_object* v_e_3294_, lean_object* v_a_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
uint8_t v_usedLetOnly_boxed_3301_; uint8_t v_skipConstInApp_boxed_3302_; uint8_t v_skipInstances_boxed_3303_; lean_object* v_res_3304_; 
v_usedLetOnly_boxed_3301_ = lean_unbox(v_usedLetOnly_3290_);
v_skipConstInApp_boxed_3302_ = lean_unbox(v_skipConstInApp_3291_);
v_skipInstances_boxed_3303_ = lean_unbox(v_skipInstances_3292_);
v_res_3304_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3288_, v_post_3289_, v_usedLetOnly_boxed_3301_, v_skipConstInApp_boxed_3302_, v_skipInstances_boxed_3303_, v_fvars_3293_, v_e_3294_, v_a_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec(v_a_3295_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3305_, lean_object* v___x_3306_, lean_object* v_pre_3307_, lean_object* v_post_3308_, lean_object* v_usedLetOnly_3309_, lean_object* v_skipConstInApp_3310_, lean_object* v_skipInstances_3311_, lean_object* v_a_3312_, lean_object* v_b_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
uint8_t v_usedLetOnly_boxed_3320_; uint8_t v_skipConstInApp_boxed_3321_; uint8_t v_skipInstances_boxed_3322_; lean_object* v_res_3323_; 
v_usedLetOnly_boxed_3320_ = lean_unbox(v_usedLetOnly_3309_);
v_skipConstInApp_boxed_3321_ = lean_unbox(v_skipConstInApp_3310_);
v_skipInstances_boxed_3322_ = lean_unbox(v_skipInstances_3311_);
v_res_3323_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3305_, v___x_3306_, v_pre_3307_, v_post_3308_, v_usedLetOnly_boxed_3320_, v_skipConstInApp_boxed_3321_, v_skipInstances_boxed_3322_, v_a_3312_, v_b_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___x_3306_);
lean_dec(v_upperBound_3305_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3324_, lean_object* v_pre_3325_, lean_object* v_post_3326_, lean_object* v_usedLetOnly_3327_, lean_object* v_skipConstInApp_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_, lean_object* v_x_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
uint8_t v_skipInstances_boxed_3338_; uint8_t v_usedLetOnly_boxed_3339_; uint8_t v_skipConstInApp_boxed_3340_; lean_object* v_res_3341_; 
v_skipInstances_boxed_3338_ = lean_unbox(v_skipInstances_3324_);
v_usedLetOnly_boxed_3339_ = lean_unbox(v_usedLetOnly_3327_);
v_skipConstInApp_boxed_3340_ = lean_unbox(v_skipConstInApp_3328_);
v_res_3341_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3338_, v_pre_3325_, v_post_3326_, v_usedLetOnly_boxed_3339_, v_skipConstInApp_boxed_3340_, v_x_3329_, v_x_3330_, v_x_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
return v_res_3341_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3342_ = lean_box(0);
v___x_3343_ = lean_unsigned_to_nat(16u);
v___x_3344_ = lean_mk_array(v___x_3343_, v___x_3342_);
return v___x_3344_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0);
v___x_3346_ = lean_unsigned_to_nat(0u);
v___x_3347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v___x_3345_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3348_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3349_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3349_, 0, lean_box(0));
lean_closure_set(v___x_3349_, 1, lean_box(0));
lean_closure_set(v___x_3349_, 2, v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3350_, lean_object* v_pre_3351_, lean_object* v_post_3352_, uint8_t v_usedLetOnly_3353_, uint8_t v_skipConstInApp_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v_a_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; 
v___x_3360_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3361_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3360_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = 0;
v___x_3364_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3351_, v_post_3352_, v_usedLetOnly_3353_, v_skipConstInApp_3354_, v___x_3363_, v_input_3350_, v_a_3362_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3364_);
v___x_3366_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3366_, 0, lean_box(0));
lean_closure_set(v___x_3366_, 1, lean_box(0));
lean_closure_set(v___x_3366_, 2, v_a_3362_);
v___x_3367_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3366_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3374_ == 0)
{
lean_object* v_unused_3375_; 
v_unused_3375_ = lean_ctor_get(v___x_3367_, 0);
lean_dec(v_unused_3375_);
v___x_3369_ = v___x_3367_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_dec(v___x_3367_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v_a_3365_);
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3365_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
else
{
lean_dec(v_a_3362_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3376_, lean_object* v_pre_3377_, lean_object* v_post_3378_, lean_object* v_usedLetOnly_3379_, lean_object* v_skipConstInApp_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
uint8_t v_usedLetOnly_boxed_3386_; uint8_t v_skipConstInApp_boxed_3387_; lean_object* v_res_3388_; 
v_usedLetOnly_boxed_3386_ = lean_unbox(v_usedLetOnly_3379_);
v_skipConstInApp_boxed_3387_ = lean_unbox(v_skipConstInApp_3380_);
v_res_3388_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3376_, v_pre_3377_, v_post_3378_, v_usedLetOnly_boxed_3386_, v_skipConstInApp_boxed_3387_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec_ref(v___y_3381_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___f_3397_; lean_object* v___f_3398_; uint8_t v___x_3399_; lean_object* v___x_3400_; 
v___f_3397_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3398_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3399_ = 0;
v___x_3400_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3391_, v___f_3398_, v___f_3397_, v___x_3399_, v___x_3399_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_upperBound_3408_, lean_object* v___x_3409_, lean_object* v_pre_3410_, lean_object* v_post_3411_, uint8_t v_usedLetOnly_3412_, uint8_t v_skipConstInApp_3413_, uint8_t v_skipInstances_3414_, lean_object* v___x_3415_, lean_object* v_inst_3416_, lean_object* v_R_3417_, lean_object* v_a_3418_, lean_object* v_b_3419_, lean_object* v_c_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3408_, v___x_3409_, v_pre_3410_, v_post_3411_, v_usedLetOnly_3412_, v_skipConstInApp_3413_, v_skipInstances_3414_, v_a_3418_, v_b_3419_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_3428_ = _args[0];
lean_object* v___x_3429_ = _args[1];
lean_object* v_pre_3430_ = _args[2];
lean_object* v_post_3431_ = _args[3];
lean_object* v_usedLetOnly_3432_ = _args[4];
lean_object* v_skipConstInApp_3433_ = _args[5];
lean_object* v_skipInstances_3434_ = _args[6];
lean_object* v___x_3435_ = _args[7];
lean_object* v_inst_3436_ = _args[8];
lean_object* v_R_3437_ = _args[9];
lean_object* v_a_3438_ = _args[10];
lean_object* v_b_3439_ = _args[11];
lean_object* v_c_3440_ = _args[12];
lean_object* v___y_3441_ = _args[13];
lean_object* v___y_3442_ = _args[14];
lean_object* v___y_3443_ = _args[15];
lean_object* v___y_3444_ = _args[16];
lean_object* v___y_3445_ = _args[17];
lean_object* v___y_3446_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3447_; uint8_t v_skipConstInApp_boxed_3448_; uint8_t v_skipInstances_boxed_3449_; lean_object* v_res_3450_; 
v_usedLetOnly_boxed_3447_ = lean_unbox(v_usedLetOnly_3432_);
v_skipConstInApp_boxed_3448_ = lean_unbox(v_skipConstInApp_3433_);
v_skipInstances_boxed_3449_ = lean_unbox(v_skipInstances_3434_);
v_res_3450_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3428_, v___x_3429_, v_pre_3430_, v_post_3431_, v_usedLetOnly_boxed_3447_, v_skipConstInApp_boxed_3448_, v_skipInstances_boxed_3449_, v___x_3435_, v_inst_3436_, v_R_3437_, v_a_3438_, v_b_3439_, v_c_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
lean_dec(v___y_3445_);
lean_dec_ref(v___y_3444_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec(v___x_3435_);
lean_dec_ref(v___x_3429_);
lean_dec(v_upperBound_3428_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_00_u03b2_3451_, lean_object* v_m_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_3452_, v_a_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3455_, lean_object* v_m_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_00_u03b2_3455_, v_m_3456_, v_a_3457_);
lean_dec_ref(v_a_3457_);
lean_dec_ref(v_m_3456_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3459_, lean_object* v_name_3460_, uint8_t v_bi_3461_, lean_object* v_type_3462_, lean_object* v_k_3463_, uint8_t v_kind_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3460_, v_bi_3461_, v_type_3462_, v_k_3463_, v_kind_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3472_, lean_object* v_name_3473_, lean_object* v_bi_3474_, lean_object* v_type_3475_, lean_object* v_k_3476_, lean_object* v_kind_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_){
_start:
{
uint8_t v_bi_boxed_3484_; uint8_t v_kind_boxed_3485_; lean_object* v_res_3486_; 
v_bi_boxed_3484_ = lean_unbox(v_bi_3474_);
v_kind_boxed_3485_ = lean_unbox(v_kind_3477_);
v_res_3486_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3472_, v_name_3473_, v_bi_boxed_3484_, v_type_3475_, v_k_3476_, v_kind_boxed_3485_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3487_, lean_object* v_name_3488_, lean_object* v_type_3489_, lean_object* v_val_3490_, lean_object* v_k_3491_, uint8_t v_nondep_3492_, uint8_t v_kind_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_){
_start:
{
lean_object* v___x_3500_; 
v___x_3500_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3488_, v_type_3489_, v_val_3490_, v_k_3491_, v_nondep_3492_, v_kind_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3501_, lean_object* v_name_3502_, lean_object* v_type_3503_, lean_object* v_val_3504_, lean_object* v_k_3505_, lean_object* v_nondep_3506_, lean_object* v_kind_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v_nondep_boxed_3514_; uint8_t v_kind_boxed_3515_; lean_object* v_res_3516_; 
v_nondep_boxed_3514_ = lean_unbox(v_nondep_3506_);
v_kind_boxed_3515_ = lean_unbox(v_kind_3507_);
v_res_3516_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3501_, v_name_3502_, v_type_3503_, v_val_3504_, v_k_3505_, v_nondep_boxed_3514_, v_kind_boxed_3515_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3517_, lean_object* v_ref_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3518_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3525_, lean_object* v_ref_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3525_, v_ref_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec_ref(v___y_3527_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3533_, lean_object* v_x_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___x_3541_; 
v___x_3541_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3542_, lean_object* v_x_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3542_, v_x_3543_, v___y_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
lean_dec(v___y_3548_);
lean_dec_ref(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
return v_res_3550_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3551_, lean_object* v_m_3552_, lean_object* v_a_3553_, lean_object* v_b_3554_){
_start:
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3552_, v_a_3553_, v_b_3554_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3556_, lean_object* v_a_3557_, lean_object* v_x_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_3557_, v_x_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b2_3560_, lean_object* v_a_3561_, lean_object* v_x_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(v_00_u03b2_3560_, v_a_3561_, v_x_3562_);
lean_dec(v_x_3562_);
lean_dec_ref(v_a_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3564_, lean_object* v_a_3565_, lean_object* v_x_3566_){
_start:
{
uint8_t v___x_3567_; 
v___x_3567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3565_, v_x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3568_, lean_object* v_a_3569_, lean_object* v_x_3570_){
_start:
{
uint8_t v_res_3571_; lean_object* v_r_3572_; 
v_res_3571_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3568_, v_a_3569_, v_x_3570_);
lean_dec(v_x_3570_);
lean_dec_ref(v_a_3569_);
v_r_3572_ = lean_box(v_res_3571_);
return v_r_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3573_, lean_object* v_data_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3576_, lean_object* v_a_3577_, lean_object* v_b_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3577_, v_b_3578_, v_x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3581_, lean_object* v_i_3582_, lean_object* v_source_3583_, lean_object* v_target_3584_){
_start:
{
lean_object* v___x_3585_; 
v___x_3585_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3582_, v_source_3583_, v_target_3584_);
return v___x_3585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3587_, v_x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3590_, lean_object* v_opt_3591_){
_start:
{
lean_object* v_name_3592_; lean_object* v_defValue_3593_; lean_object* v_map_3594_; lean_object* v___x_3595_; 
v_name_3592_ = lean_ctor_get(v_opt_3591_, 0);
v_defValue_3593_ = lean_ctor_get(v_opt_3591_, 1);
v_map_3594_ = lean_ctor_get(v_opts_3590_, 0);
v___x_3595_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3594_, v_name_3592_);
if (lean_obj_tag(v___x_3595_) == 0)
{
uint8_t v___x_3596_; 
v___x_3596_ = lean_unbox(v_defValue_3593_);
return v___x_3596_;
}
else
{
lean_object* v_val_3597_; 
v_val_3597_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_val_3597_);
lean_dec_ref(v___x_3595_);
if (lean_obj_tag(v_val_3597_) == 1)
{
uint8_t v_v_3598_; 
v_v_3598_ = lean_ctor_get_uint8(v_val_3597_, 0);
lean_dec_ref(v_val_3597_);
return v_v_3598_;
}
else
{
uint8_t v___x_3599_; 
lean_dec(v_val_3597_);
v___x_3599_ = lean_unbox(v_defValue_3593_);
return v___x_3599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3600_, lean_object* v_opt_3601_){
_start:
{
uint8_t v_res_3602_; lean_object* v_r_3603_; 
v_res_3602_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3600_, v_opt_3601_);
lean_dec_ref(v_opt_3601_);
lean_dec_ref(v_opts_3600_);
v_r_3603_ = lean_box(v_res_3602_);
return v_r_3603_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3604_; 
v___x_3604_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3604_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_3606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3607_){
_start:
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1);
return v___x_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(lean_object* v_e_3609_, lean_object* v_k_3610_, uint8_t v_cleanupAnnotations_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v___f_3617_; uint8_t v___x_3618_; uint8_t v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___f_3617_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3617_, 0, v_k_3610_);
v___x_3618_ = 1;
v___x_3619_ = 0;
v___x_3620_ = lean_box(0);
v___x_3621_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3609_, v___x_3618_, v___x_3619_, v___x_3618_, v___x_3619_, v___x_3620_, v___f_3617_, v_cleanupAnnotations_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3621_);
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
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
v_a_3630_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3621_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3621_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg___boxed(lean_object* v_e_3638_, lean_object* v_k_3639_, lean_object* v_cleanupAnnotations_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3646_; lean_object* v_res_3647_; 
v_cleanupAnnotations_boxed_3646_ = lean_unbox(v_cleanupAnnotations_3640_);
v_res_3647_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3638_, v_k_3639_, v_cleanupAnnotations_boxed_3646_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_00_u03b1_3648_, lean_object* v_e_3649_, lean_object* v_k_3650_, uint8_t v_cleanupAnnotations_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v___x_3657_; 
v___x_3657_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3649_, v_k_3650_, v_cleanupAnnotations_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_00_u03b1_3658_, lean_object* v_e_3659_, lean_object* v_k_3660_, lean_object* v_cleanupAnnotations_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3667_; lean_object* v_res_3668_; 
v_cleanupAnnotations_boxed_3667_ = lean_unbox(v_cleanupAnnotations_3661_);
v_res_3668_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(v_00_u03b1_3658_, v_e_3659_, v_k_3660_, v_cleanupAnnotations_boxed_3667_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3669_, lean_object* v_x_3670_, lean_object* v_x_3671_){
_start:
{
if (lean_obj_tag(v_x_3669_) == 5)
{
lean_object* v_fn_3676_; lean_object* v_arg_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; 
v_fn_3676_ = lean_ctor_get(v_x_3669_, 0);
lean_inc_ref(v_fn_3676_);
v_arg_3677_ = lean_ctor_get(v_x_3669_, 1);
lean_inc_ref(v_arg_3677_);
lean_dec_ref(v_x_3669_);
v___x_3678_ = lean_array_set(v_x_3670_, v_x_3671_, v_arg_3677_);
v___x_3679_ = lean_unsigned_to_nat(1u);
v___x_3680_ = lean_nat_sub(v_x_3671_, v___x_3679_);
lean_dec(v_x_3671_);
v_x_3669_ = v_fn_3676_;
v_x_3670_ = v___x_3678_;
v_x_3671_ = v___x_3680_;
goto _start;
}
else
{
lean_object* v___x_3682_; uint8_t v___x_3683_; 
lean_dec(v_x_3671_);
v___x_3682_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3683_ = l_Lean_Expr_isConstOf(v_x_3669_, v___x_3682_);
lean_dec_ref(v_x_3669_);
if (v___x_3683_ == 0)
{
lean_dec_ref(v_x_3670_);
goto v___jp_3673_;
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v___x_3684_ = lean_unsigned_to_nat(2u);
v___x_3685_ = lean_array_get_size(v_x_3670_);
v___x_3686_ = lean_nat_dec_le(v___x_3684_, v___x_3685_);
if (v___x_3686_ == 0)
{
lean_dec_ref(v_x_3670_);
goto v___jp_3673_;
}
else
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = lean_array_fget(v_x_3670_, v___x_3687_);
v___x_3689_ = l_Array_toSubarray___redArg(v_x_3670_, v___x_3684_, v___x_3685_);
v___x_3690_ = l_Subarray_copy___redArg(v___x_3689_);
v___x_3691_ = l_Lean_mkAppN(v___x_3688_, v___x_3690_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
v___x_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
return v___x_3694_;
}
}
}
v___jp_3673_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
return v___x_3675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3695_, lean_object* v_x_3696_, lean_object* v_x_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v_res_3699_; 
v_res_3699_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3695_, v_x_3696_, v_x_3697_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(lean_object* v_e_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_dummy_3706_; lean_object* v_nargs_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; 
v_dummy_3706_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3707_ = l_Lean_Expr_getAppNumArgs(v_e_3700_);
lean_inc(v_nargs_3707_);
v___x_3708_ = lean_mk_array(v_nargs_3707_, v_dummy_3706_);
v___x_3709_ = lean_unsigned_to_nat(1u);
v___x_3710_ = lean_nat_sub(v_nargs_3707_, v___x_3709_);
lean_dec(v_nargs_3707_);
v___x_3711_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3700_, v___x_3708_, v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v_e_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_Elab_WF_preprocess___lam__0(v_e_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(lean_object* v_ref_3719_){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3721_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_ref_3719_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_ref_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3724_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(lean_object* v_x_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v___y_3735_; lean_object* v_fileName_3744_; lean_object* v_fileMap_3745_; lean_object* v_options_3746_; lean_object* v_currRecDepth_3747_; lean_object* v_maxRecDepth_3748_; lean_object* v_ref_3749_; lean_object* v_currNamespace_3750_; lean_object* v_openDecls_3751_; lean_object* v_initHeartbeats_3752_; lean_object* v_maxHeartbeats_3753_; lean_object* v_quotContext_3754_; lean_object* v_currMacroScope_3755_; uint8_t v_diag_3756_; lean_object* v_cancelTk_x3f_3757_; uint8_t v_suppressElabErrors_3758_; lean_object* v_inheritedTraceOptions_3759_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v_fileName_3744_ = lean_ctor_get(v___y_3731_, 0);
v_fileMap_3745_ = lean_ctor_get(v___y_3731_, 1);
v_options_3746_ = lean_ctor_get(v___y_3731_, 2);
v_currRecDepth_3747_ = lean_ctor_get(v___y_3731_, 3);
v_maxRecDepth_3748_ = lean_ctor_get(v___y_3731_, 4);
v_ref_3749_ = lean_ctor_get(v___y_3731_, 5);
v_currNamespace_3750_ = lean_ctor_get(v___y_3731_, 6);
v_openDecls_3751_ = lean_ctor_get(v___y_3731_, 7);
v_initHeartbeats_3752_ = lean_ctor_get(v___y_3731_, 8);
v_maxHeartbeats_3753_ = lean_ctor_get(v___y_3731_, 9);
v_quotContext_3754_ = lean_ctor_get(v___y_3731_, 10);
v_currMacroScope_3755_ = lean_ctor_get(v___y_3731_, 11);
v_diag_3756_ = lean_ctor_get_uint8(v___y_3731_, sizeof(void*)*14);
v_cancelTk_x3f_3757_ = lean_ctor_get(v___y_3731_, 12);
v_suppressElabErrors_3758_ = lean_ctor_get_uint8(v___y_3731_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3759_ = lean_ctor_get(v___y_3731_, 13);
v___x_3765_ = lean_unsigned_to_nat(0u);
v___x_3766_ = lean_nat_dec_eq(v_maxRecDepth_3748_, v___x_3765_);
if (v___x_3766_ == 0)
{
uint8_t v___x_3767_; 
v___x_3767_ = lean_nat_dec_eq(v_currRecDepth_3747_, v_maxRecDepth_3748_);
if (v___x_3767_ == 0)
{
goto v___jp_3760_;
}
else
{
lean_object* v___x_3768_; 
lean_dec_ref(v_x_3727_);
lean_inc(v_ref_3749_);
v___x_3768_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3749_);
v___y_3735_ = v___x_3768_;
goto v___jp_3734_;
}
}
else
{
goto v___jp_3760_;
}
v___jp_3734_:
{
if (lean_obj_tag(v___y_3735_) == 0)
{
return v___y_3735_;
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
v_a_3736_ = lean_ctor_get(v___y_3735_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___y_3735_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___y_3735_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___y_3735_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
v___jp_3760_:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3761_ = lean_unsigned_to_nat(1u);
v___x_3762_ = lean_nat_add(v_currRecDepth_3747_, v___x_3761_);
lean_inc_ref(v_inheritedTraceOptions_3759_);
lean_inc(v_cancelTk_x3f_3757_);
lean_inc(v_currMacroScope_3755_);
lean_inc(v_quotContext_3754_);
lean_inc(v_maxHeartbeats_3753_);
lean_inc(v_initHeartbeats_3752_);
lean_inc(v_openDecls_3751_);
lean_inc(v_currNamespace_3750_);
lean_inc(v_ref_3749_);
lean_inc(v_maxRecDepth_3748_);
lean_inc_ref(v_options_3746_);
lean_inc_ref(v_fileMap_3745_);
lean_inc_ref(v_fileName_3744_);
v___x_3763_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3763_, 0, v_fileName_3744_);
lean_ctor_set(v___x_3763_, 1, v_fileMap_3745_);
lean_ctor_set(v___x_3763_, 2, v_options_3746_);
lean_ctor_set(v___x_3763_, 3, v___x_3762_);
lean_ctor_set(v___x_3763_, 4, v_maxRecDepth_3748_);
lean_ctor_set(v___x_3763_, 5, v_ref_3749_);
lean_ctor_set(v___x_3763_, 6, v_currNamespace_3750_);
lean_ctor_set(v___x_3763_, 7, v_openDecls_3751_);
lean_ctor_set(v___x_3763_, 8, v_initHeartbeats_3752_);
lean_ctor_set(v___x_3763_, 9, v_maxHeartbeats_3753_);
lean_ctor_set(v___x_3763_, 10, v_quotContext_3754_);
lean_ctor_set(v___x_3763_, 11, v_currMacroScope_3755_);
lean_ctor_set(v___x_3763_, 12, v_cancelTk_x3f_3757_);
lean_ctor_set(v___x_3763_, 13, v_inheritedTraceOptions_3759_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*14, v_diag_3756_);
lean_ctor_set_uint8(v___x_3763_, sizeof(void*)*14 + 1, v_suppressElabErrors_3758_);
lean_inc(v___y_3732_);
lean_inc(v___y_3730_);
lean_inc_ref(v___y_3729_);
lean_inc(v___y_3728_);
v___x_3764_ = lean_apply_6(v_x_3727_, v___y_3728_, v___y_3729_, v___y_3730_, v___x_3763_, v___y_3732_, lean_box(0));
v___y_3735_ = v___x_3764_;
goto v___jp_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg___boxed(lean_object* v_x_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
lean_dec(v___y_3770_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(lean_object* v_pre_3777_, lean_object* v_post_3778_, size_t v_sz_3779_, size_t v_i_3780_, lean_object* v_bs_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_lt(v_i_3780_, v_sz_3779_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; 
lean_dec_ref(v_post_3778_);
lean_dec_ref(v_pre_3777_);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_bs_3781_);
return v___x_3789_;
}
else
{
lean_object* v_v_3790_; lean_object* v___x_3791_; 
v_v_3790_ = lean_array_uget_borrowed(v_bs_3781_, v_i_3780_);
lean_inc(v_v_3790_);
lean_inc_ref(v_post_3778_);
lean_inc_ref(v_pre_3777_);
v___x_3791_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3777_, v_post_3778_, v_v_3790_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; lean_object* v_bs_x27_3794_; size_t v___x_3795_; size_t v___x_3796_; lean_object* v___x_3797_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___x_3791_);
v___x_3793_ = lean_unsigned_to_nat(0u);
v_bs_x27_3794_ = lean_array_uset(v_bs_3781_, v_i_3780_, v___x_3793_);
v___x_3795_ = ((size_t)1ULL);
v___x_3796_ = lean_usize_add(v_i_3780_, v___x_3795_);
v___x_3797_ = lean_array_uset(v_bs_x27_3794_, v_i_3780_, v_a_3792_);
v_i_3780_ = v___x_3796_;
v_bs_3781_ = v___x_3797_;
goto _start;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_bs_3781_);
lean_dec_ref(v_post_3778_);
lean_dec_ref(v_pre_3777_);
v_a_3799_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3791_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3791_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_3807_, lean_object* v_post_3808_, lean_object* v_x_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_){
_start:
{
if (lean_obj_tag(v_x_3809_) == 5)
{
lean_object* v_fn_3818_; lean_object* v_arg_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v_fn_3818_ = lean_ctor_get(v_x_3809_, 0);
lean_inc_ref(v_fn_3818_);
v_arg_3819_ = lean_ctor_get(v_x_3809_, 1);
lean_inc_ref(v_arg_3819_);
lean_dec_ref(v_x_3809_);
v___x_3820_ = lean_array_set(v_x_3810_, v_x_3811_, v_arg_3819_);
v___x_3821_ = lean_unsigned_to_nat(1u);
v___x_3822_ = lean_nat_sub(v_x_3811_, v___x_3821_);
lean_dec(v_x_3811_);
v_x_3809_ = v_fn_3818_;
v_x_3810_ = v___x_3820_;
v_x_3811_ = v___x_3822_;
goto _start;
}
else
{
lean_object* v___x_3824_; 
lean_dec(v_x_3811_);
lean_inc_ref(v_post_3808_);
lean_inc_ref(v_pre_3807_);
v___x_3824_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3807_, v_post_3808_, v_x_3809_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; size_t v_sz_3826_; size_t v___x_3827_; lean_object* v___x_3828_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref(v___x_3824_);
v_sz_3826_ = lean_array_size(v_x_3810_);
v___x_3827_ = ((size_t)0ULL);
lean_inc_ref(v_post_3808_);
lean_inc_ref(v_pre_3807_);
v___x_3828_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_3807_, v_post_3808_, v_sz_3826_, v___x_3827_, v_x_3810_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref(v___x_3828_);
v___x_3830_ = l_Lean_mkAppN(v_a_3825_, v_a_3829_);
lean_dec(v_a_3829_);
v___x_3831_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3807_, v_post_3808_, v___x_3830_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
return v___x_3831_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v_a_3825_);
lean_dec_ref(v_post_3808_);
lean_dec_ref(v_pre_3807_);
v_a_3832_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3828_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3828_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
else
{
lean_dec_ref(v_x_3810_);
lean_dec_ref(v_post_3808_);
lean_dec_ref(v_pre_3807_);
return v___x_3824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v___x_3840_, lean_object* v_pre_3841_, lean_object* v_e_3842_, lean_object* v_post_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; uint8_t v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; uint8_t v___y_3858_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; uint8_t v___y_3871_; lean_object* v___y_3872_; uint8_t v___y_3873_; lean_object* v___y_3881_; uint8_t v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; uint8_t v___y_3886_; lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_Core_checkSystem(v___x_3840_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v___x_3894_; 
lean_dec_ref(v___x_3893_);
lean_inc_ref(v_pre_3841_);
lean_inc(v___y_3848_);
lean_inc_ref(v___y_3847_);
lean_inc(v___y_3846_);
lean_inc_ref(v___y_3845_);
lean_inc_ref(v_e_3842_);
v___x_3894_ = lean_apply_6(v_pre_3841_, v_e_3842_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, lean_box(0));
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3984_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3984_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3984_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___y_3900_; 
switch(lean_obj_tag(v_a_3895_))
{
case 0:
{
lean_object* v_e_3974_; lean_object* v___x_3976_; 
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_e_3842_);
lean_dec_ref(v_pre_3841_);
v_e_3974_ = lean_ctor_get(v_a_3895_, 0);
lean_inc_ref(v_e_3974_);
lean_dec_ref(v_a_3895_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v_e_3974_);
v___x_3976_ = v___x_3897_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_e_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
case 1:
{
lean_object* v_e_3978_; lean_object* v___x_3979_; 
lean_del_object(v___x_3897_);
lean_dec_ref(v_e_3842_);
v_e_3978_ = lean_ctor_get(v_a_3895_, 0);
lean_inc_ref(v_e_3978_);
lean_dec_ref(v_a_3895_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3979_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_e_3978_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3981_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc(v_a_3980_);
lean_dec_ref(v___x_3979_);
v___x_3981_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v_a_3980_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3981_;
}
else
{
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3979_;
}
}
default: 
{
lean_object* v_e_x3f_3982_; 
lean_del_object(v___x_3897_);
v_e_x3f_3982_ = lean_ctor_get(v_a_3895_, 0);
lean_inc(v_e_x3f_3982_);
lean_dec_ref(v_a_3895_);
if (lean_obj_tag(v_e_x3f_3982_) == 0)
{
v___y_3900_ = v_e_3842_;
goto v___jp_3899_;
}
else
{
lean_object* v_val_3983_; 
lean_dec_ref(v_e_3842_);
v_val_3983_ = lean_ctor_get(v_e_x3f_3982_, 0);
lean_inc(v_val_3983_);
lean_dec_ref(v_e_x3f_3982_);
v___y_3900_ = v_val_3983_;
goto v___jp_3899_;
}
}
}
v___jp_3899_:
{
switch(lean_obj_tag(v___y_3900_))
{
case 7:
{
lean_object* v_binderName_3901_; lean_object* v_binderType_3902_; lean_object* v_body_3903_; uint8_t v_binderInfo_3904_; lean_object* v___x_3905_; 
v_binderName_3901_ = lean_ctor_get(v___y_3900_, 0);
lean_inc(v_binderName_3901_);
v_binderType_3902_ = lean_ctor_get(v___y_3900_, 1);
v_body_3903_ = lean_ctor_get(v___y_3900_, 2);
v_binderInfo_3904_ = lean_ctor_get_uint8(v___y_3900_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3902_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3905_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_binderType_3902_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3907_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref(v___x_3905_);
lean_inc_ref(v_body_3903_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3907_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_body_3903_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; size_t v___x_3909_; size_t v___x_3910_; uint8_t v___x_3911_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = lean_ptr_addr(v_binderType_3902_);
v___x_3910_ = lean_ptr_addr(v_a_3906_);
v___x_3911_ = lean_usize_dec_eq(v___x_3909_, v___x_3910_);
if (v___x_3911_ == 0)
{
v___y_3881_ = v_binderName_3901_;
v___y_3882_ = v_binderInfo_3904_;
v___y_3883_ = v___y_3900_;
v___y_3884_ = v_a_3908_;
v___y_3885_ = v_a_3906_;
v___y_3886_ = v___x_3911_;
goto v___jp_3880_;
}
else
{
size_t v___x_3912_; size_t v___x_3913_; uint8_t v___x_3914_; 
v___x_3912_ = lean_ptr_addr(v_body_3903_);
v___x_3913_ = lean_ptr_addr(v_a_3908_);
v___x_3914_ = lean_usize_dec_eq(v___x_3912_, v___x_3913_);
v___y_3881_ = v_binderName_3901_;
v___y_3882_ = v_binderInfo_3904_;
v___y_3883_ = v___y_3900_;
v___y_3884_ = v_a_3908_;
v___y_3885_ = v_a_3906_;
v___y_3886_ = v___x_3914_;
goto v___jp_3880_;
}
}
else
{
lean_dec(v_a_3906_);
lean_dec(v_binderName_3901_);
lean_dec_ref(v___y_3900_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3907_;
}
}
else
{
lean_dec_ref(v___y_3900_);
lean_dec(v_binderName_3901_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3905_;
}
}
case 6:
{
lean_object* v_binderName_3915_; lean_object* v_binderType_3916_; lean_object* v_body_3917_; uint8_t v_binderInfo_3918_; lean_object* v___x_3919_; 
v_binderName_3915_ = lean_ctor_get(v___y_3900_, 0);
lean_inc(v_binderName_3915_);
v_binderType_3916_ = lean_ctor_get(v___y_3900_, 1);
v_body_3917_ = lean_ctor_get(v___y_3900_, 2);
v_binderInfo_3918_ = lean_ctor_get_uint8(v___y_3900_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3916_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3919_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_binderType_3916_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3921_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref(v___x_3919_);
lean_inc_ref(v_body_3917_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3921_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_body_3917_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; size_t v___x_3923_; size_t v___x_3924_; uint8_t v___x_3925_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref(v___x_3921_);
v___x_3923_ = lean_ptr_addr(v_binderType_3916_);
v___x_3924_ = lean_ptr_addr(v_a_3920_);
v___x_3925_ = lean_usize_dec_eq(v___x_3923_, v___x_3924_);
if (v___x_3925_ == 0)
{
v___y_3868_ = v_binderName_3915_;
v___y_3869_ = v_a_3922_;
v___y_3870_ = v___y_3900_;
v___y_3871_ = v_binderInfo_3918_;
v___y_3872_ = v_a_3920_;
v___y_3873_ = v___x_3925_;
goto v___jp_3867_;
}
else
{
size_t v___x_3926_; size_t v___x_3927_; uint8_t v___x_3928_; 
v___x_3926_ = lean_ptr_addr(v_body_3917_);
v___x_3927_ = lean_ptr_addr(v_a_3922_);
v___x_3928_ = lean_usize_dec_eq(v___x_3926_, v___x_3927_);
v___y_3868_ = v_binderName_3915_;
v___y_3869_ = v_a_3922_;
v___y_3870_ = v___y_3900_;
v___y_3871_ = v_binderInfo_3918_;
v___y_3872_ = v_a_3920_;
v___y_3873_ = v___x_3928_;
goto v___jp_3867_;
}
}
else
{
lean_dec(v_a_3920_);
lean_dec(v_binderName_3915_);
lean_dec_ref(v___y_3900_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3921_;
}
}
else
{
lean_dec(v_binderName_3915_);
lean_dec_ref(v___y_3900_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3919_;
}
}
case 8:
{
lean_object* v_declName_3929_; lean_object* v_type_3930_; lean_object* v_value_3931_; lean_object* v_body_3932_; uint8_t v_nondep_3933_; lean_object* v___x_3934_; 
v_declName_3929_ = lean_ctor_get(v___y_3900_, 0);
lean_inc(v_declName_3929_);
v_type_3930_ = lean_ctor_get(v___y_3900_, 1);
v_value_3931_ = lean_ctor_get(v___y_3900_, 2);
v_body_3932_ = lean_ctor_get(v___y_3900_, 3);
lean_inc_ref(v_body_3932_);
v_nondep_3933_ = lean_ctor_get_uint8(v___y_3900_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3930_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3934_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_type_3930_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3936_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref(v___x_3934_);
lean_inc_ref(v_value_3931_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3936_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_value_3931_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v___x_3938_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_a_3937_);
lean_dec_ref(v___x_3936_);
lean_inc_ref(v_body_3932_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3938_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_body_3932_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; size_t v___x_3940_; size_t v___x_3941_; uint8_t v___x_3942_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref(v___x_3938_);
v___x_3940_ = lean_ptr_addr(v_type_3930_);
v___x_3941_ = lean_ptr_addr(v_a_3935_);
v___x_3942_ = lean_usize_dec_eq(v___x_3940_, v___x_3941_);
if (v___x_3942_ == 0)
{
v___y_3851_ = v_a_3939_;
v___y_3852_ = v___y_3900_;
v___y_3853_ = v_body_3932_;
v___y_3854_ = v_a_3935_;
v___y_3855_ = v_nondep_3933_;
v___y_3856_ = v_a_3937_;
v___y_3857_ = v_declName_3929_;
v___y_3858_ = v___x_3942_;
goto v___jp_3850_;
}
else
{
size_t v___x_3943_; size_t v___x_3944_; uint8_t v___x_3945_; 
v___x_3943_ = lean_ptr_addr(v_value_3931_);
v___x_3944_ = lean_ptr_addr(v_a_3937_);
v___x_3945_ = lean_usize_dec_eq(v___x_3943_, v___x_3944_);
v___y_3851_ = v_a_3939_;
v___y_3852_ = v___y_3900_;
v___y_3853_ = v_body_3932_;
v___y_3854_ = v_a_3935_;
v___y_3855_ = v_nondep_3933_;
v___y_3856_ = v_a_3937_;
v___y_3857_ = v_declName_3929_;
v___y_3858_ = v___x_3945_;
goto v___jp_3850_;
}
}
else
{
lean_dec(v_a_3937_);
lean_dec(v_a_3935_);
lean_dec_ref(v_body_3932_);
lean_dec(v_declName_3929_);
lean_dec_ref(v___y_3900_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3938_;
}
}
else
{
lean_dec(v_a_3935_);
lean_dec_ref(v_body_3932_);
lean_dec_ref(v___y_3900_);
lean_dec(v_declName_3929_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3936_;
}
}
else
{
lean_dec_ref(v_body_3932_);
lean_dec_ref(v___y_3900_);
lean_dec(v_declName_3929_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3934_;
}
}
case 5:
{
lean_object* v_dummy_3946_; lean_object* v_nargs_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; 
v_dummy_3946_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3947_ = l_Lean_Expr_getAppNumArgs(v___y_3900_);
lean_inc(v_nargs_3947_);
v___x_3948_ = lean_mk_array(v_nargs_3947_, v_dummy_3946_);
v___x_3949_ = lean_unsigned_to_nat(1u);
v___x_3950_ = lean_nat_sub(v_nargs_3947_, v___x_3949_);
lean_dec(v_nargs_3947_);
v___x_3951_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3841_, v_post_3843_, v___y_3900_, v___x_3948_, v___x_3950_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3951_;
}
case 10:
{
lean_object* v_data_3952_; lean_object* v_expr_3953_; lean_object* v___x_3954_; 
v_data_3952_ = lean_ctor_get(v___y_3900_, 0);
v_expr_3953_ = lean_ctor_get(v___y_3900_, 1);
lean_inc_ref(v_expr_3953_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3954_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_expr_3953_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; size_t v___x_3956_; size_t v___x_3957_; uint8_t v___x_3958_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref(v___x_3954_);
v___x_3956_ = lean_ptr_addr(v_expr_3953_);
v___x_3957_ = lean_ptr_addr(v_a_3955_);
v___x_3958_ = lean_usize_dec_eq(v___x_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
lean_inc(v_data_3952_);
lean_dec_ref(v___y_3900_);
v___x_3959_ = l_Lean_Expr_mdata___override(v_data_3952_, v_a_3955_);
v___x_3960_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3959_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; 
lean_dec(v_a_3955_);
v___x_3961_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___y_3900_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3961_;
}
}
else
{
lean_dec_ref(v___y_3900_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3954_;
}
}
case 11:
{
lean_object* v_typeName_3962_; lean_object* v_idx_3963_; lean_object* v_struct_3964_; lean_object* v___x_3965_; 
v_typeName_3962_ = lean_ctor_get(v___y_3900_, 0);
v_idx_3963_ = lean_ctor_get(v___y_3900_, 1);
v_struct_3964_ = lean_ctor_get(v___y_3900_, 2);
lean_inc_ref(v_struct_3964_);
lean_inc_ref(v_post_3843_);
lean_inc_ref(v_pre_3841_);
v___x_3965_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3841_, v_post_3843_, v_struct_3964_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; size_t v___x_3967_; size_t v___x_3968_; uint8_t v___x_3969_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref(v___x_3965_);
v___x_3967_ = lean_ptr_addr(v_struct_3964_);
v___x_3968_ = lean_ptr_addr(v_a_3966_);
v___x_3969_ = lean_usize_dec_eq(v___x_3967_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
lean_inc(v_idx_3963_);
lean_inc(v_typeName_3962_);
lean_dec_ref(v___y_3900_);
v___x_3970_ = l_Lean_Expr_proj___override(v_typeName_3962_, v_idx_3963_, v_a_3966_);
v___x_3971_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3970_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3971_;
}
else
{
lean_object* v___x_3972_; 
lean_dec(v_a_3966_);
v___x_3972_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___y_3900_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3972_;
}
}
else
{
lean_dec_ref(v___y_3900_);
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_pre_3841_);
return v___x_3965_;
}
}
default: 
{
lean_object* v___x_3973_; 
v___x_3973_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___y_3900_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3973_;
}
}
}
}
}
else
{
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_e_3842_);
lean_dec_ref(v_pre_3841_);
v_a_3985_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3894_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3894_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v_post_3843_);
lean_dec_ref(v_e_3842_);
lean_dec_ref(v_pre_3841_);
v_a_3993_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3893_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3893_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
v___jp_3850_:
{
if (v___y_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_dec_ref(v___y_3853_);
lean_dec_ref(v___y_3852_);
v___x_3859_ = l_Lean_Expr_letE___override(v___y_3857_, v___y_3854_, v___y_3856_, v___y_3851_, v___y_3855_);
v___x_3860_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3859_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3860_;
}
else
{
size_t v___x_3861_; size_t v___x_3862_; uint8_t v___x_3863_; 
v___x_3861_ = lean_ptr_addr(v___y_3853_);
lean_dec_ref(v___y_3853_);
v___x_3862_ = lean_ptr_addr(v___y_3851_);
v___x_3863_ = lean_usize_dec_eq(v___x_3861_, v___x_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_dec_ref(v___y_3852_);
v___x_3864_ = l_Lean_Expr_letE___override(v___y_3857_, v___y_3854_, v___y_3856_, v___y_3851_, v___y_3855_);
v___x_3865_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3864_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3865_;
}
else
{
lean_object* v___x_3866_; 
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec_ref(v___y_3854_);
lean_dec_ref(v___y_3851_);
v___x_3866_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___y_3852_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3866_;
}
}
}
v___jp_3867_:
{
if (v___y_3873_ == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
lean_dec_ref(v___y_3870_);
v___x_3874_ = l_Lean_Expr_lam___override(v___y_3868_, v___y_3872_, v___y_3869_, v___y_3871_);
v___x_3875_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3874_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3875_;
}
else
{
uint8_t v___x_3876_; 
v___x_3876_ = l_Lean_instBEqBinderInfo_beq(v___y_3871_, v___y_3871_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
lean_dec_ref(v___y_3870_);
v___x_3877_ = l_Lean_Expr_lam___override(v___y_3868_, v___y_3872_, v___y_3869_, v___y_3871_);
v___x_3878_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3877_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; 
lean_dec_ref(v___y_3872_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
v___x_3879_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___y_3870_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3879_;
}
}
}
v___jp_3880_:
{
if (v___y_3886_ == 0)
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
lean_dec_ref(v___y_3883_);
v___x_3887_ = l_Lean_Expr_forallE___override(v___y_3881_, v___y_3885_, v___y_3884_, v___y_3882_);
v___x_3888_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3887_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3888_;
}
else
{
uint8_t v___x_3889_; 
v___x_3889_ = l_Lean_instBEqBinderInfo_beq(v___y_3882_, v___y_3882_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
lean_dec_ref(v___y_3883_);
v___x_3890_ = l_Lean_Expr_forallE___override(v___y_3881_, v___y_3885_, v___y_3884_, v___y_3882_);
v___x_3891_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___x_3890_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3891_;
}
else
{
lean_object* v___x_3892_; 
lean_dec_ref(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3881_);
v___x_3892_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3841_, v_post_3843_, v___y_3883_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_);
return v___x_3892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v___x_4001_, lean_object* v_pre_4002_, lean_object* v_e_4003_, lean_object* v_post_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v___x_4001_, v_pre_4002_, v_e_4003_, v_post_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
lean_dec(v___y_4005_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_4012_, lean_object* v_post_4013_, lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
lean_inc(v_a_4015_);
v___x_4021_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4021_, 0, lean_box(0));
lean_closure_set(v___x_4021_, 1, lean_box(0));
lean_closure_set(v___x_4021_, 2, v_a_4015_);
v___x_4022_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_4021_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4054_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4025_ = v___x_4022_;
v_isShared_4026_ = v_isSharedCheck_4054_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4022_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4054_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_4023_, v_e_4014_);
lean_dec(v_a_4023_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v___x_4028_; lean_object* v___f_4029_; lean_object* v___x_4030_; 
lean_del_object(v___x_4025_);
v___x_4028_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___closed__0));
lean_inc_ref(v_e_4014_);
v___f_4029_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4029_, 0, v___x_4028_);
lean_closure_set(v___f_4029_, 1, v_pre_4012_);
lean_closure_set(v___f_4029_, 2, v_e_4014_);
lean_closure_set(v___f_4029_, 3, v_post_4013_);
v___x_4030_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v___f_4029_, v_a_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___f_4032_; lean_object* v___x_4033_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc_n(v_a_4031_, 2);
lean_dec_ref(v___x_4030_);
lean_inc(v_a_4015_);
v___f_4032_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4032_, 0, v_a_4015_);
lean_closure_set(v___f_4032_, 1, v_e_4014_);
lean_closure_set(v___f_4032_, 2, v_a_4031_);
v___x_4033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_4032_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4040_ == 0)
{
lean_object* v_unused_4041_; 
v_unused_4041_ = lean_ctor_get(v___x_4033_, 0);
lean_dec(v_unused_4041_);
v___x_4035_ = v___x_4033_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_dec(v___x_4033_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v_a_4031_);
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4031_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec(v_a_4031_);
v_a_4042_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4033_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4033_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
else
{
lean_dec_ref(v_e_4014_);
return v___x_4030_;
}
}
else
{
lean_object* v_val_4050_; lean_object* v___x_4052_; 
lean_dec_ref(v_e_4014_);
lean_dec_ref(v_post_4013_);
lean_dec_ref(v_pre_4012_);
v_val_4050_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_val_4050_);
lean_dec_ref(v___x_4027_);
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v_val_4050_);
v___x_4052_ = v___x_4025_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_val_4050_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
else
{
lean_object* v_a_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4062_; 
lean_dec_ref(v_e_4014_);
lean_dec_ref(v_post_4013_);
lean_dec_ref(v_pre_4012_);
v_a_4055_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_4057_ = v___x_4022_;
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_a_4055_);
lean_dec(v___x_4022_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4062_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v___x_4060_; 
if (v_isShared_4058_ == 0)
{
v___x_4060_ = v___x_4057_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4055_);
v___x_4060_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
return v___x_4060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_4063_, lean_object* v_post_4064_, lean_object* v_e_4065_, lean_object* v_a_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; 
lean_inc_ref(v_post_4064_);
lean_inc(v___y_4070_);
lean_inc_ref(v___y_4069_);
lean_inc(v___y_4068_);
lean_inc_ref(v___y_4067_);
lean_inc_ref(v_e_4065_);
v___x_4072_ = lean_apply_6(v_post_4064_, v_e_4065_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, lean_box(0));
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4091_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4091_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4091_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
switch(lean_obj_tag(v_a_4073_))
{
case 0:
{
lean_object* v_e_4077_; lean_object* v___x_4079_; 
lean_dec_ref(v_e_4065_);
lean_dec_ref(v_post_4064_);
lean_dec_ref(v_pre_4063_);
v_e_4077_ = lean_ctor_get(v_a_4073_, 0);
lean_inc_ref(v_e_4077_);
lean_dec_ref(v_a_4073_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v_e_4077_);
v___x_4079_ = v___x_4075_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_e_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
case 1:
{
lean_object* v_e_4081_; lean_object* v___x_4082_; 
lean_del_object(v___x_4075_);
lean_dec_ref(v_e_4065_);
v_e_4081_ = lean_ctor_get(v_a_4073_, 0);
lean_inc_ref(v_e_4081_);
lean_dec_ref(v_a_4073_);
v___x_4082_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4063_, v_post_4064_, v_e_4081_, v_a_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
return v___x_4082_;
}
default: 
{
lean_object* v_e_x3f_4083_; 
lean_dec_ref(v_post_4064_);
lean_dec_ref(v_pre_4063_);
v_e_x3f_4083_ = lean_ctor_get(v_a_4073_, 0);
lean_inc(v_e_x3f_4083_);
lean_dec_ref(v_a_4073_);
if (lean_obj_tag(v_e_x3f_4083_) == 0)
{
lean_object* v___x_4085_; 
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v_e_4065_);
v___x_4085_ = v___x_4075_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_e_4065_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
else
{
lean_object* v_val_4087_; lean_object* v___x_4089_; 
lean_dec_ref(v_e_4065_);
v_val_4087_ = lean_ctor_get(v_e_x3f_4083_, 0);
lean_inc(v_val_4087_);
lean_dec_ref(v_e_x3f_4083_);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v_val_4087_);
v___x_4089_ = v___x_4075_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_val_4087_);
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
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v_e_4065_);
lean_dec_ref(v_post_4064_);
lean_dec_ref(v_pre_4063_);
v_a_4092_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4072_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4072_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4100_, lean_object* v_post_4101_, lean_object* v_e_4102_, lean_object* v_a_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4100_, v_post_4101_, v_e_4102_, v_a_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v_a_4103_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6___boxed(lean_object* v_pre_4110_, lean_object* v_post_4111_, lean_object* v_sz_4112_, lean_object* v_i_4113_, lean_object* v_bs_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
size_t v_sz_boxed_4121_; size_t v_i_boxed_4122_; lean_object* v_res_4123_; 
v_sz_boxed_4121_ = lean_unbox_usize(v_sz_4112_);
lean_dec(v_sz_4112_);
v_i_boxed_4122_ = lean_unbox_usize(v_i_4113_);
lean_dec(v_i_4113_);
v_res_4123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_4110_, v_post_4111_, v_sz_boxed_4121_, v_i_boxed_4122_, v_bs_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4124_, lean_object* v_post_4125_, lean_object* v_x_4126_, lean_object* v_x_4127_, lean_object* v_x_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4124_, v_post_4125_, v_x_4126_, v_x_4127_, v_x_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object* v_pre_4136_, lean_object* v_post_4137_, lean_object* v_e_4138_, lean_object* v_a_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4136_, v_post_4137_, v_e_4138_, v_a_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v_a_4139_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object* v_input_4146_, lean_object* v_pre_4147_, lean_object* v_post_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v_a_4156_; lean_object* v___x_4157_; 
v___x_4154_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_4155_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4154_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref(v___x_4155_);
v___x_4157_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4147_, v_post_4148_, v_input_4146_, v_a_4156_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref(v___x_4157_);
v___x_4159_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4159_, 0, lean_box(0));
lean_closure_set(v___x_4159_, 1, lean_box(0));
lean_closure_set(v___x_4159_, 2, v_a_4156_);
v___x_4160_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4159_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4167_ == 0)
{
lean_object* v_unused_4168_; 
v_unused_4168_ = lean_ctor_get(v___x_4160_, 0);
lean_dec(v_unused_4168_);
v___x_4162_ = v___x_4160_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_dec(v___x_4160_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
lean_ctor_set(v___x_4162_, 0, v_a_4158_);
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4158_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
else
{
lean_dec(v_a_4156_);
return v___x_4157_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object* v_input_4169_, lean_object* v_pre_4170_, lean_object* v_post_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4169_, v_pre_4170_, v_post_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
return v_res_4177_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4178_; double v___x_4179_; 
v___x_4178_ = lean_unsigned_to_nat(0u);
v___x_4179_ = lean_float_of_nat(v___x_4178_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_4183_, lean_object* v_msg_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_ref_4190_; lean_object* v___x_4191_; lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4236_; 
v_ref_4190_ = lean_ctor_get(v___y_4187_, 5);
v___x_4191_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4236_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4236_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v_traceState_4197_; lean_object* v_env_4198_; lean_object* v_nextMacroScope_4199_; lean_object* v_ngen_4200_; lean_object* v_auxDeclNGen_4201_; lean_object* v_cache_4202_; lean_object* v_messages_4203_; lean_object* v_infoState_4204_; lean_object* v_snapshotTasks_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4235_; 
v___x_4196_ = lean_st_ref_take(v___y_4188_);
v_traceState_4197_ = lean_ctor_get(v___x_4196_, 4);
v_env_4198_ = lean_ctor_get(v___x_4196_, 0);
v_nextMacroScope_4199_ = lean_ctor_get(v___x_4196_, 1);
v_ngen_4200_ = lean_ctor_get(v___x_4196_, 2);
v_auxDeclNGen_4201_ = lean_ctor_get(v___x_4196_, 3);
v_cache_4202_ = lean_ctor_get(v___x_4196_, 5);
v_messages_4203_ = lean_ctor_get(v___x_4196_, 6);
v_infoState_4204_ = lean_ctor_get(v___x_4196_, 7);
v_snapshotTasks_4205_ = lean_ctor_get(v___x_4196_, 8);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4207_ = v___x_4196_;
v_isShared_4208_ = v_isSharedCheck_4235_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_snapshotTasks_4205_);
lean_inc(v_infoState_4204_);
lean_inc(v_messages_4203_);
lean_inc(v_cache_4202_);
lean_inc(v_traceState_4197_);
lean_inc(v_auxDeclNGen_4201_);
lean_inc(v_ngen_4200_);
lean_inc(v_nextMacroScope_4199_);
lean_inc(v_env_4198_);
lean_dec(v___x_4196_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4235_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
uint64_t v_tid_4209_; lean_object* v_traces_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4234_; 
v_tid_4209_ = lean_ctor_get_uint64(v_traceState_4197_, sizeof(void*)*1);
v_traces_4210_ = lean_ctor_get(v_traceState_4197_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v_traceState_4197_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4212_ = v_traceState_4197_;
v_isShared_4213_ = v_isSharedCheck_4234_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_traces_4210_);
lean_dec(v_traceState_4197_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4234_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4214_; double v___x_4215_; uint8_t v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4214_ = lean_box(0);
v___x_4215_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0);
v___x_4216_ = 0;
v___x_4217_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1));
v___x_4218_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4218_, 0, v_cls_4183_);
lean_ctor_set(v___x_4218_, 1, v___x_4214_);
lean_ctor_set(v___x_4218_, 2, v___x_4217_);
lean_ctor_set_float(v___x_4218_, sizeof(void*)*3, v___x_4215_);
lean_ctor_set_float(v___x_4218_, sizeof(void*)*3 + 8, v___x_4215_);
lean_ctor_set_uint8(v___x_4218_, sizeof(void*)*3 + 16, v___x_4216_);
v___x_4219_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2));
v___x_4220_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4220_, 0, v___x_4218_);
lean_ctor_set(v___x_4220_, 1, v_a_4192_);
lean_ctor_set(v___x_4220_, 2, v___x_4219_);
lean_inc(v_ref_4190_);
v___x_4221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4221_, 0, v_ref_4190_);
lean_ctor_set(v___x_4221_, 1, v___x_4220_);
v___x_4222_ = l_Lean_PersistentArray_push___redArg(v_traces_4210_, v___x_4221_);
if (v_isShared_4213_ == 0)
{
lean_ctor_set(v___x_4212_, 0, v___x_4222_);
v___x_4224_ = v___x_4212_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v___x_4222_);
lean_ctor_set_uint64(v_reuseFailAlloc_4233_, sizeof(void*)*1, v_tid_4209_);
v___x_4224_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
lean_object* v___x_4226_; 
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 4, v___x_4224_);
v___x_4226_ = v___x_4207_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_env_4198_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v_nextMacroScope_4199_);
lean_ctor_set(v_reuseFailAlloc_4232_, 2, v_ngen_4200_);
lean_ctor_set(v_reuseFailAlloc_4232_, 3, v_auxDeclNGen_4201_);
lean_ctor_set(v_reuseFailAlloc_4232_, 4, v___x_4224_);
lean_ctor_set(v_reuseFailAlloc_4232_, 5, v_cache_4202_);
lean_ctor_set(v_reuseFailAlloc_4232_, 6, v_messages_4203_);
lean_ctor_set(v_reuseFailAlloc_4232_, 7, v_infoState_4204_);
lean_ctor_set(v_reuseFailAlloc_4232_, 8, v_snapshotTasks_4205_);
v___x_4226_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4230_; 
v___x_4227_ = lean_st_ref_set(v___y_4188_, v___x_4226_);
v___x_4228_ = lean_box(0);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4228_);
v___x_4230_ = v___x_4194_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v___x_4228_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_4237_, lean_object* v_msg_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_4237_, v_msg_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4245_, size_t v_i_4246_, lean_object* v_bs_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
uint8_t v___x_4253_; 
v___x_4253_ = lean_usize_dec_lt(v_i_4246_, v_sz_4245_);
if (v___x_4253_ == 0)
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4254_, 0, v_bs_4247_);
return v___x_4254_;
}
else
{
lean_object* v_v_4255_; lean_object* v___x_4256_; 
v_v_4255_ = lean_array_uget_borrowed(v_bs_4247_, v_i_4246_);
lean_inc(v_v_4255_);
v___x_4256_ = l_Lean_Elab_WF_mkWfParam(v_v_4255_, v___y_4248_, v___y_4249_, v___y_4250_, v___y_4251_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; lean_object* v_bs_x27_4259_; size_t v___x_4260_; size_t v___x_4261_; lean_object* v___x_4262_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref(v___x_4256_);
v___x_4258_ = lean_unsigned_to_nat(0u);
v_bs_x27_4259_ = lean_array_uset(v_bs_4247_, v_i_4246_, v___x_4258_);
v___x_4260_ = ((size_t)1ULL);
v___x_4261_ = lean_usize_add(v_i_4246_, v___x_4260_);
v___x_4262_ = lean_array_uset(v_bs_x27_4259_, v_i_4246_, v_a_4257_);
v_i_4246_ = v___x_4261_;
v_bs_4247_ = v___x_4262_;
goto _start;
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec_ref(v_bs_4247_);
v_a_4264_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4256_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4256_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4272_, lean_object* v_i_4273_, lean_object* v_bs_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
size_t v_sz_boxed_4280_; size_t v_i_boxed_4281_; lean_object* v_res_4282_; 
v_sz_boxed_4280_ = lean_unbox_usize(v_sz_4272_);
lean_dec(v_sz_4272_);
v_i_boxed_4281_ = lean_unbox_usize(v_i_4273_);
lean_dec(v_i_4273_);
v_res_4282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4280_, v_i_boxed_4281_, v_bs_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
return v_res_4282_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_4283_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_box(0));
return v___x_4284_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4285_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__1, &l_Lean_Elab_WF_preprocess___lam__2___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1);
v___x_4286_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__0, &l_Lean_Elab_WF_preprocess___lam__2___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0);
v___x_4287_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
lean_ctor_set(v___x_4287_, 2, v___x_4285_);
lean_ctor_set(v___x_4287_, 3, v___x_4285_);
return v___x_4287_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3(void){
_start:
{
lean_object* v___x_4288_; 
v___x_4288_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4288_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4(void){
_start:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__3, &l_Lean_Elab_WF_preprocess___lam__2___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3);
v___x_4290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4290_, 0, v___x_4289_);
return v___x_4290_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5(void){
_start:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4291_ = lean_unsigned_to_nat(0u);
v___x_4292_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
lean_ctor_set(v___x_4293_, 1, v___x_4291_);
return v___x_4293_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
v___x_4294_ = lean_unsigned_to_nat(32u);
v___x_4295_ = lean_mk_empty_array_with_capacity(v___x_4294_);
v___x_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
return v___x_4296_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7(void){
_start:
{
size_t v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4297_ = ((size_t)5ULL);
v___x_4298_ = lean_unsigned_to_nat(0u);
v___x_4299_ = lean_unsigned_to_nat(32u);
v___x_4300_ = lean_mk_empty_array_with_capacity(v___x_4299_);
v___x_4301_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__6, &l_Lean_Elab_WF_preprocess___lam__2___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6);
v___x_4302_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4302_, 0, v___x_4301_);
lean_ctor_set(v___x_4302_, 1, v___x_4300_);
lean_ctor_set(v___x_4302_, 2, v___x_4298_);
lean_ctor_set(v___x_4302_, 3, v___x_4298_);
lean_ctor_set_usize(v___x_4302_, 4, v___x_4297_);
return v___x_4302_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__8(void){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4303_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__7, &l_Lean_Elab_WF_preprocess___lam__2___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7);
v___x_4304_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4305_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
lean_ctor_set(v___x_4305_, 2, v___x_4304_);
lean_ctor_set(v___x_4305_, 3, v___x_4303_);
return v___x_4305_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__9(void){
_start:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4306_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__8, &l_Lean_Elab_WF_preprocess___lam__2___closed__8_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__8);
v___x_4307_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__5, &l_Lean_Elab_WF_preprocess___lam__2___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5);
v___x_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v___x_4306_);
return v___x_4308_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14(void){
_start:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v___x_4317_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4318_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__13));
v___x_4319_ = l_Lean_Name_append(v___x_4318_, v___x_4317_);
return v___x_4319_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__15));
v___x_4322_ = l_Lean_stringToMessageData(v___x_4321_);
return v___x_4322_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__17));
v___x_4325_ = l_Lean_stringToMessageData(v___x_4324_);
return v___x_4325_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__20(void){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__19));
v___x_4328_ = l_Lean_stringToMessageData(v___x_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2(uint8_t v___x_4329_, lean_object* v_a_4330_, lean_object* v___f_4331_, lean_object* v___f_4332_, lean_object* v_xs_4333_, lean_object* v_x_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
size_t v_sz_4340_; size_t v___x_4341_; lean_object* v___x_4342_; 
v_sz_4340_ = lean_array_size(v_xs_4333_);
v___x_4341_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4333_);
v___x_4342_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4340_, v___x_4341_, v_xs_4333_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4343_);
lean_dec_ref(v___x_4342_);
v___x_4344_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4345_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_4346_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4344_, v___x_4345_, v___x_4329_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4348_; uint8_t v___x_4349_; lean_object* v___x_4350_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref(v___x_4346_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_4349_ = 0;
v___x_4350_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4347_, v___x_4348_, v___x_4349_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref(v___x_4350_);
v___x_4352_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_4353_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4351_, v___x_4352_, v___x_4329_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref(v___x_4353_);
v___x_4355_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4335_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref(v___x_4355_);
v___x_4357_ = l_Lean_Expr_beta(v_a_4330_, v_a_4343_);
v___x_4358_ = lean_unsigned_to_nat(1u);
v___x_4359_ = lean_mk_empty_array_with_capacity(v___x_4358_);
v___x_4360_ = lean_array_push(v___x_4359_, v_a_4354_);
v___x_4361_ = lean_box(0);
v___x_4362_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__9, &l_Lean_Elab_WF_preprocess___lam__2___closed__9_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__9);
lean_inc_ref(v___x_4357_);
v___x_4363_ = l_Lean_Meta_simp(v___x_4357_, v_a_4356_, v___x_4360_, v___x_4361_, v___x_4362_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; lean_object* v_fst_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4433_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref(v___x_4363_);
v_fst_4365_ = lean_ctor_get(v_a_4364_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v_a_4364_);
if (v_isSharedCheck_4433_ == 0)
{
lean_object* v_unused_4434_; 
v_unused_4434_ = lean_ctor_get(v_a_4364_, 1);
lean_dec(v_unused_4434_);
v___x_4367_ = v_a_4364_;
v_isShared_4368_ = v_isSharedCheck_4433_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_fst_4365_);
lean_dec(v_a_4364_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4433_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v_expr_4369_; lean_object* v_proof_x3f_4370_; uint8_t v_cache_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4432_; 
v_expr_4369_ = lean_ctor_get(v_fst_4365_, 0);
v_proof_x3f_4370_ = lean_ctor_get(v_fst_4365_, 1);
v_cache_4371_ = lean_ctor_get_uint8(v_fst_4365_, sizeof(void*)*2);
v_isSharedCheck_4432_ = !lean_is_exclusive(v_fst_4365_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4373_ = v_fst_4365_;
v_isShared_4374_ = v_isSharedCheck_4432_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_proof_x3f_4370_);
lean_inc(v_expr_4369_);
lean_dec(v_fst_4365_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4432_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4375_; 
lean_inc_ref(v_expr_4369_);
v___x_4375_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4369_, v___f_4331_, v___f_4332_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4377_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
lean_dec_ref(v___x_4375_);
v___x_4377_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4376_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4377_) == 0)
{
lean_object* v_a_4378_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v_options_4388_; uint8_t v_hasTrace_4389_; 
v_a_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_a_4378_);
lean_dec_ref(v___x_4377_);
v_options_4388_ = lean_ctor_get(v___y_4337_, 2);
v_hasTrace_4389_ = lean_ctor_get_uint8(v_options_4388_, sizeof(void*)*1);
if (v_hasTrace_4389_ == 0)
{
lean_dec_ref(v_expr_4369_);
lean_del_object(v___x_4367_);
lean_dec_ref(v___x_4357_);
v___y_4380_ = v___y_4335_;
v___y_4381_ = v___y_4336_;
v___y_4382_ = v___y_4337_;
v___y_4383_ = v___y_4338_;
goto v___jp_4379_;
}
else
{
lean_object* v_inheritedTraceOptions_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v_inheritedTraceOptions_4390_ = lean_ctor_get(v___y_4337_, 13);
v___x_4391_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4392_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__14, &l_Lean_Elab_WF_preprocess___lam__2___closed__14_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4390_, v_options_4388_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_dec_ref(v_expr_4369_);
lean_del_object(v___x_4367_);
lean_dec_ref(v___x_4357_);
v___y_4380_ = v___y_4335_;
v___y_4381_ = v___y_4336_;
v___y_4382_ = v___y_4337_;
v___y_4383_ = v___y_4338_;
goto v___jp_4379_;
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4397_; 
v___x_4394_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__16, &l_Lean_Elab_WF_preprocess___lam__2___closed__16_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16);
v___x_4395_ = l_Lean_indentExpr(v___x_4357_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set_tag(v___x_4367_, 7);
lean_ctor_set(v___x_4367_, 1, v___x_4395_);
lean_ctor_set(v___x_4367_, 0, v___x_4394_);
v___x_4397_ = v___x_4367_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4394_);
lean_ctor_set(v_reuseFailAlloc_4415_, 1, v___x_4395_);
v___x_4397_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4398_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__18, &l_Lean_Elab_WF_preprocess___lam__2___closed__18_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18);
v___x_4399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4397_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = l_Lean_indentExpr(v_expr_4369_);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4399_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__20, &l_Lean_Elab_WF_preprocess___lam__2___closed__20_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__20);
v___x_4403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4403_, 0, v___x_4401_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
lean_inc(v_a_4378_);
v___x_4404_ = l_Lean_indentExpr(v_a_4378_);
v___x_4405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4403_);
lean_ctor_set(v___x_4405_, 1, v___x_4404_);
v___x_4406_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v___x_4391_, v___x_4405_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_dec_ref(v___x_4406_);
v___y_4380_ = v___y_4335_;
v___y_4381_ = v___y_4336_;
v___y_4382_ = v___y_4337_;
v___y_4383_ = v___y_4338_;
goto v___jp_4379_;
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec(v_a_4378_);
lean_del_object(v___x_4373_);
lean_dec(v_proof_x3f_4370_);
lean_dec_ref(v_xs_4333_);
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4406_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4406_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
}
}
v___jp_4379_:
{
lean_object* v___x_4385_; 
if (v_isShared_4374_ == 0)
{
lean_ctor_set(v___x_4373_, 0, v_a_4378_);
v___x_4385_ = v___x_4373_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4378_);
lean_ctor_set(v_reuseFailAlloc_4387_, 1, v_proof_x3f_4370_);
lean_ctor_set_uint8(v_reuseFailAlloc_4387_, sizeof(void*)*2, v_cache_4371_);
v___x_4385_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4385_, v_xs_4333_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
lean_dec_ref(v_xs_4333_);
return v___x_4386_;
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_del_object(v___x_4373_);
lean_dec(v_proof_x3f_4370_);
lean_dec_ref(v_expr_4369_);
lean_del_object(v___x_4367_);
lean_dec_ref(v___x_4357_);
lean_dec_ref(v_xs_4333_);
v_a_4416_ = lean_ctor_get(v___x_4377_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4377_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4377_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4377_);
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
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_del_object(v___x_4373_);
lean_dec(v_proof_x3f_4370_);
lean_dec_ref(v_expr_4369_);
lean_del_object(v___x_4367_);
lean_dec_ref(v___x_4357_);
lean_dec_ref(v_xs_4333_);
v_a_4424_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4375_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4375_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec_ref(v___x_4357_);
lean_dec_ref(v_xs_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v___f_4331_);
v_a_4435_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4363_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4363_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
else
{
lean_object* v_a_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec(v_a_4354_);
lean_dec(v_a_4343_);
lean_dec_ref(v_xs_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_a_4330_);
v_a_4443_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4355_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_a_4443_);
lean_dec(v___x_4355_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_a_4343_);
lean_dec_ref(v_xs_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_a_4330_);
v_a_4451_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4353_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4353_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_dec(v_a_4343_);
lean_dec_ref(v_xs_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_a_4330_);
v_a_4459_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4350_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4350_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec(v_a_4343_);
lean_dec_ref(v_xs_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_a_4330_);
v_a_4467_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4346_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4346_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec_ref(v_xs_4333_);
lean_dec_ref(v___f_4332_);
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_a_4330_);
v_a_4475_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4342_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4342_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2___boxed(lean_object* v___x_4483_, lean_object* v_a_4484_, lean_object* v___f_4485_, lean_object* v___f_4486_, lean_object* v_xs_4487_, lean_object* v_x_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
uint8_t v___x_14797__boxed_4494_; lean_object* v_res_4495_; 
v___x_14797__boxed_4494_ = lean_unbox(v___x_4483_);
v_res_4495_ = l_Lean_Elab_WF_preprocess___lam__2(v___x_14797__boxed_4494_, v_a_4484_, v___f_4485_, v___f_4486_, v_xs_4487_, v_x_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec_ref(v_x_4488_);
return v_res_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_){
_start:
{
lean_object* v_options_4503_; lean_object* v___x_4504_; uint8_t v___x_4505_; uint8_t v___x_4506_; 
v_options_4503_ = lean_ctor_get(v_a_4500_, 2);
v___x_4504_ = l_wf_preprocess;
v___x_4505_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_options_4503_, v___x_4504_);
v___x_4506_ = 1;
if (v___x_4505_ == 0)
{
lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v___x_4507_ = lean_box(0);
v___x_4508_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4508_, 0, v_e_4497_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
lean_ctor_set_uint8(v___x_4508_, sizeof(void*)*2, v___x_4506_);
v___x_4509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4509_, 0, v___x_4508_);
return v___x_4509_;
}
else
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_Meta_letToHave(v_e_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
if (lean_obj_tag(v___x_4510_) == 0)
{
lean_object* v_a_4511_; lean_object* v___f_4512_; lean_object* v___f_4513_; lean_object* v___x_4514_; lean_object* v___f_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; 
v_a_4511_ = lean_ctor_get(v___x_4510_, 0);
lean_inc_n(v_a_4511_, 2);
lean_dec_ref(v___x_4510_);
v___f_4512_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___f_4513_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___x_4514_ = lean_box(v___x_4506_);
v___f_4515_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__2___boxed), 11, 4);
lean_closure_set(v___f_4515_, 0, v___x_4514_);
lean_closure_set(v___f_4515_, 1, v_a_4511_);
lean_closure_set(v___f_4515_, 2, v___f_4512_);
lean_closure_set(v___f_4515_, 3, v___f_4513_);
v___x_4516_ = 0;
v___x_4517_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_a_4511_, v___f_4515_, v___x_4516_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
return v___x_4517_;
}
else
{
lean_object* v_a_4518_; lean_object* v___x_4520_; uint8_t v_isShared_4521_; uint8_t v_isSharedCheck_4525_; 
v_a_4518_ = lean_ctor_get(v___x_4510_, 0);
v_isSharedCheck_4525_ = !lean_is_exclusive(v___x_4510_);
if (v_isSharedCheck_4525_ == 0)
{
v___x_4520_ = v___x_4510_;
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
else
{
lean_inc(v_a_4518_);
lean_dec(v___x_4510_);
v___x_4520_ = lean_box(0);
v_isShared_4521_ = v_isSharedCheck_4525_;
goto v_resetjp_4519_;
}
v_resetjp_4519_:
{
lean_object* v___x_4523_; 
if (v_isShared_4521_ == 0)
{
v___x_4523_ = v___x_4520_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4524_; 
v_reuseFailAlloc_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4524_, 0, v_a_4518_);
v___x_4523_ = v_reuseFailAlloc_4524_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
return v___x_4523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = l_Lean_Elab_WF_preprocess(v_e_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4533_, lean_object* v_x_4534_, lean_object* v_x_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4533_, v_x_4534_, v_x_4535_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4542_, lean_object* v_x_4543_, lean_object* v_x_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4542_, v_x_4543_, v_x_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4547_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
return v_res_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_4551_, lean_object* v_ref_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_4552_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4557_, lean_object* v_ref_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_res_4562_; 
v_res_4562_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(v_00_u03b1_4557_, v_ref_4558_, v___y_4559_, v___y_4560_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
return v_res_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_00_u03b1_4563_, lean_object* v_x_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_00_u03b1_4572_, lean_object* v_x_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_00_u03b1_4572_, v_x_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
return v_res_4580_;
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
res = l_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_4121217895____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_wf_preprocess = lean_io_result_get_value(res);
lean_mark_persistent(l_wf_preprocess);
lean_dec_ref(res);
res = l_Lean_Elab_WF_initFn_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_1389474921____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_WF_wfPreprocessSimpExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_WF_wfPreprocessSimpExtension);
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_WF_paramProj___regBuiltin_Lean_Elab_WF_paramProj_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_WF_paramMatcher___regBuiltin_Lean_Elab_WF_paramMatcher_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_14_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_WF_paramLet___regBuiltin_Lean_Elab_WF_paramLet_declare__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_14_();
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
