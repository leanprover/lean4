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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_624_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
lean_ctor_set(v___x_624_, 2, v___x_623_);
lean_ctor_set(v___x_624_, 3, v___x_622_);
lean_ctor_set(v___x_624_, 4, v___x_622_);
lean_ctor_set(v___x_624_, 5, v___x_622_);
lean_ctor_set(v___x_624_, 6, v___x_622_);
lean_ctor_set(v___x_624_, 7, v___x_622_);
lean_ctor_set(v___x_624_, 8, v___x_622_);
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
uint8_t v_a_10678__boxed_2144_; lean_object* v_res_2145_; 
v_a_10678__boxed_2144_ = lean_unbox(v_a_2135_);
v_res_2145_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___lam__1(v_a_10678__boxed_2144_, v_lctx_2136_, v_xs_2137_, v_b_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
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
lean_object* v___y_2251_; lean_object* v_fileName_2260_; lean_object* v_fileMap_2261_; lean_object* v_options_2262_; lean_object* v_currRecDepth_2263_; lean_object* v_maxRecDepth_2264_; lean_object* v_ref_2265_; lean_object* v_currNamespace_2266_; lean_object* v_openDecls_2267_; lean_object* v_initHeartbeats_2268_; lean_object* v_maxHeartbeats_2269_; lean_object* v_quotContext_2270_; lean_object* v_currMacroScope_2271_; uint8_t v_diag_2272_; lean_object* v_cancelTk_x3f_2273_; uint8_t v_suppressElabErrors_2274_; lean_object* v_inheritedTraceOptions_2275_; uint8_t v___x_2276_; 
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
v___x_2276_ = lean_nat_dec_eq(v_currRecDepth_2263_, v_maxRecDepth_2264_);
if (v___x_2276_ == 0)
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
else
{
lean_object* v___x_2281_; 
lean_dec_ref(v_x_2243_);
lean_inc(v_ref_2265_);
v___x_2281_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_2265_);
v___y_2251_ = v___x_2281_;
goto v___jp_2250_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg___boxed(lean_object* v_x_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(lean_object* v_a_2290_, lean_object* v_x_2291_){
_start:
{
if (lean_obj_tag(v_x_2291_) == 0)
{
lean_object* v___x_2292_; 
v___x_2292_ = lean_box(0);
return v___x_2292_;
}
else
{
lean_object* v_key_2293_; lean_object* v_value_2294_; lean_object* v_tail_2295_; uint8_t v___x_2296_; 
v_key_2293_ = lean_ctor_get(v_x_2291_, 0);
v_value_2294_ = lean_ctor_get(v_x_2291_, 1);
v_tail_2295_ = lean_ctor_get(v_x_2291_, 2);
v___x_2296_ = l_Lean_ExprStructEq_beq(v_key_2293_, v_a_2290_);
if (v___x_2296_ == 0)
{
v_x_2291_ = v_tail_2295_;
goto _start;
}
else
{
lean_object* v___x_2298_; 
lean_inc(v_value_2294_);
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v_value_2294_);
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_a_2299_, lean_object* v_x_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2299_, v_x_2300_);
lean_dec(v_x_2300_);
lean_dec_ref(v_a_2299_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(lean_object* v_m_2302_, lean_object* v_a_2303_){
_start:
{
lean_object* v_buckets_2304_; lean_object* v___x_2305_; uint64_t v___x_2306_; uint64_t v___x_2307_; uint64_t v___x_2308_; uint64_t v_fold_2309_; uint64_t v___x_2310_; uint64_t v___x_2311_; uint64_t v___x_2312_; size_t v___x_2313_; size_t v___x_2314_; size_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_buckets_2304_ = lean_ctor_get(v_m_2302_, 1);
v___x_2305_ = lean_array_get_size(v_buckets_2304_);
v___x_2306_ = l_Lean_ExprStructEq_hash(v_a_2303_);
v___x_2307_ = 32ULL;
v___x_2308_ = lean_uint64_shift_right(v___x_2306_, v___x_2307_);
v_fold_2309_ = lean_uint64_xor(v___x_2306_, v___x_2308_);
v___x_2310_ = 16ULL;
v___x_2311_ = lean_uint64_shift_right(v_fold_2309_, v___x_2310_);
v___x_2312_ = lean_uint64_xor(v_fold_2309_, v___x_2311_);
v___x_2313_ = lean_uint64_to_usize(v___x_2312_);
v___x_2314_ = lean_usize_of_nat(v___x_2305_);
v___x_2315_ = ((size_t)1ULL);
v___x_2316_ = lean_usize_sub(v___x_2314_, v___x_2315_);
v___x_2317_ = lean_usize_land(v___x_2313_, v___x_2316_);
v___x_2318_ = lean_array_uget_borrowed(v_buckets_2304_, v___x_2317_);
v___x_2319_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_2303_, v___x_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg___boxed(lean_object* v_m_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_2320_, v_a_2321_);
lean_dec_ref(v_a_2321_);
lean_dec_ref(v_m_2320_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(lean_object* v_k_2323_, lean_object* v___y_2324_, lean_object* v_b_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; 
lean_inc(v___y_2329_);
lean_inc_ref(v___y_2328_);
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
lean_inc(v___y_2324_);
v___x_2331_ = lean_apply_7(v_k_2323_, v_b_2325_, v___y_2324_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, lean_box(0));
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed(lean_object* v_k_2332_, lean_object* v___y_2333_, lean_object* v_b_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0(v_k_2332_, v___y_2333_, v_b_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2333_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(lean_object* v_name_2341_, uint8_t v_bi_2342_, lean_object* v_type_2343_, lean_object* v_k_2344_, uint8_t v_kind_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v___f_2352_; lean_object* v___x_2353_; 
lean_inc(v___y_2346_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2352_, 0, v_k_2344_);
lean_closure_set(v___f_2352_, 1, v___y_2346_);
v___x_2353_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2341_, v_bi_2342_, v_type_2343_, v___f_2352_, v_kind_2345_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
if (lean_obj_tag(v___x_2353_) == 0)
{
return v___x_2353_;
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___boxed(lean_object* v_name_2362_, lean_object* v_bi_2363_, lean_object* v_type_2364_, lean_object* v_k_2365_, lean_object* v_kind_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v_bi_boxed_2373_; uint8_t v_kind_boxed_2374_; lean_object* v_res_2375_; 
v_bi_boxed_2373_ = lean_unbox(v_bi_2363_);
v_kind_boxed_2374_ = lean_unbox(v_kind_2366_);
v_res_2375_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_2362_, v_bi_boxed_2373_, v_type_2364_, v_k_2365_, v_kind_boxed_2374_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(lean_object* v___x_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2376_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2(v___x_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(lean_object* v_name_2390_, lean_object* v_type_2391_, lean_object* v_val_2392_, lean_object* v_k_2393_, uint8_t v_nondep_2394_, uint8_t v_kind_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___f_2402_; lean_object* v___x_2403_; 
lean_inc(v___y_2396_);
v___f_2402_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_2402_, 0, v_k_2393_);
lean_closure_set(v___f_2402_, 1, v___y_2396_);
v___x_2403_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_2390_, v_type_2391_, v_val_2392_, v___f_2402_, v_nondep_2394_, v_kind_2395_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2403_) == 0)
{
return v___x_2403_;
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg___boxed(lean_object* v_name_2412_, lean_object* v_type_2413_, lean_object* v_val_2414_, lean_object* v_k_2415_, lean_object* v_nondep_2416_, lean_object* v_kind_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v_nondep_boxed_2424_; uint8_t v_kind_boxed_2425_; lean_object* v_res_2426_; 
v_nondep_boxed_2424_ = lean_unbox(v_nondep_2416_);
v_kind_boxed_2425_ = lean_unbox(v_kind_2417_);
v_res_2426_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_2412_, v_type_2413_, v_val_2414_, v_k_2415_, v_nondep_boxed_2424_, v_kind_boxed_2425_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_object* v_00_u03b1_2427_, lean_object* v_x_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_apply_1(v_x_2428_, lean_box(0));
v___x_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0___boxed(lean_object* v_00_u03b1_2436_, lean_object* v_x_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(v_00_u03b1_2436_, v_x_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
return v_res_2443_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(lean_object* v_a_2444_, lean_object* v_x_2445_){
_start:
{
if (lean_obj_tag(v_x_2445_) == 0)
{
uint8_t v___x_2446_; 
v___x_2446_ = 0;
return v___x_2446_;
}
else
{
lean_object* v_key_2447_; lean_object* v_tail_2448_; uint8_t v___x_2449_; 
v_key_2447_ = lean_ctor_get(v_x_2445_, 0);
v_tail_2448_ = lean_ctor_get(v_x_2445_, 2);
v___x_2449_ = l_Lean_ExprStructEq_beq(v_key_2447_, v_a_2444_);
if (v___x_2449_ == 0)
{
v_x_2445_ = v_tail_2448_;
goto _start;
}
else
{
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg___boxed(lean_object* v_a_2451_, lean_object* v_x_2452_){
_start:
{
uint8_t v_res_2453_; lean_object* v_r_2454_; 
v_res_2453_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2451_, v_x_2452_);
lean_dec(v_x_2452_);
lean_dec_ref(v_a_2451_);
v_r_2454_ = lean_box(v_res_2453_);
return v_r_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(lean_object* v_a_2455_, lean_object* v_b_2456_, lean_object* v_x_2457_){
_start:
{
if (lean_obj_tag(v_x_2457_) == 0)
{
lean_dec(v_b_2456_);
lean_dec_ref(v_a_2455_);
return v_x_2457_;
}
else
{
lean_object* v_key_2458_; lean_object* v_value_2459_; lean_object* v_tail_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2472_; 
v_key_2458_ = lean_ctor_get(v_x_2457_, 0);
v_value_2459_ = lean_ctor_get(v_x_2457_, 1);
v_tail_2460_ = lean_ctor_get(v_x_2457_, 2);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_x_2457_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2462_ = v_x_2457_;
v_isShared_2463_ = v_isSharedCheck_2472_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_tail_2460_);
lean_inc(v_value_2459_);
lean_inc(v_key_2458_);
lean_dec(v_x_2457_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2472_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
uint8_t v___x_2464_; 
v___x_2464_ = l_Lean_ExprStructEq_beq(v_key_2458_, v_a_2455_);
if (v___x_2464_ == 0)
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
v___x_2465_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2455_, v_b_2456_, v_tail_2460_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 2, v___x_2465_);
v___x_2467_ = v___x_2462_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_key_2458_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_value_2459_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
else
{
lean_object* v___x_2470_; 
lean_dec(v_value_2459_);
lean_dec(v_key_2458_);
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v_b_2456_);
lean_ctor_set(v___x_2462_, 0, v_a_2455_);
v___x_2470_ = v___x_2462_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2455_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_b_2456_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_tail_2460_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(lean_object* v_x_2473_, lean_object* v_x_2474_){
_start:
{
if (lean_obj_tag(v_x_2474_) == 0)
{
return v_x_2473_;
}
else
{
lean_object* v_key_2475_; lean_object* v_value_2476_; lean_object* v_tail_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2500_; 
v_key_2475_ = lean_ctor_get(v_x_2474_, 0);
v_value_2476_ = lean_ctor_get(v_x_2474_, 1);
v_tail_2477_ = lean_ctor_get(v_x_2474_, 2);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_x_2474_);
if (v_isSharedCheck_2500_ == 0)
{
v___x_2479_ = v_x_2474_;
v_isShared_2480_ = v_isSharedCheck_2500_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_tail_2477_);
lean_inc(v_value_2476_);
lean_inc(v_key_2475_);
lean_dec(v_x_2474_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2500_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; uint64_t v___x_2482_; uint64_t v___x_2483_; uint64_t v___x_2484_; uint64_t v_fold_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; size_t v___x_2489_; size_t v___x_2490_; size_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2481_ = lean_array_get_size(v_x_2473_);
v___x_2482_ = l_Lean_ExprStructEq_hash(v_key_2475_);
v___x_2483_ = 32ULL;
v___x_2484_ = lean_uint64_shift_right(v___x_2482_, v___x_2483_);
v_fold_2485_ = lean_uint64_xor(v___x_2482_, v___x_2484_);
v___x_2486_ = 16ULL;
v___x_2487_ = lean_uint64_shift_right(v_fold_2485_, v___x_2486_);
v___x_2488_ = lean_uint64_xor(v_fold_2485_, v___x_2487_);
v___x_2489_ = lean_uint64_to_usize(v___x_2488_);
v___x_2490_ = lean_usize_of_nat(v___x_2481_);
v___x_2491_ = ((size_t)1ULL);
v___x_2492_ = lean_usize_sub(v___x_2490_, v___x_2491_);
v___x_2493_ = lean_usize_land(v___x_2489_, v___x_2492_);
v___x_2494_ = lean_array_uget_borrowed(v_x_2473_, v___x_2493_);
lean_inc(v___x_2494_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 2, v___x_2494_);
v___x_2496_ = v___x_2479_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_key_2475_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_value_2476_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; 
v___x_2497_ = lean_array_uset(v_x_2473_, v___x_2493_, v___x_2496_);
v_x_2473_ = v___x_2497_;
v_x_2474_ = v_tail_2477_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(lean_object* v_i_2501_, lean_object* v_source_2502_, lean_object* v_target_2503_){
_start:
{
lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2504_ = lean_array_get_size(v_source_2502_);
v___x_2505_ = lean_nat_dec_lt(v_i_2501_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_dec_ref(v_source_2502_);
lean_dec(v_i_2501_);
return v_target_2503_;
}
else
{
lean_object* v_es_2506_; lean_object* v___x_2507_; lean_object* v_source_2508_; lean_object* v_target_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v_es_2506_ = lean_array_fget(v_source_2502_, v_i_2501_);
v___x_2507_ = lean_box(0);
v_source_2508_ = lean_array_fset(v_source_2502_, v_i_2501_, v___x_2507_);
v_target_2509_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_target_2503_, v_es_2506_);
v___x_2510_ = lean_unsigned_to_nat(1u);
v___x_2511_ = lean_nat_add(v_i_2501_, v___x_2510_);
lean_dec(v_i_2501_);
v_i_2501_ = v___x_2511_;
v_source_2502_ = v_source_2508_;
v_target_2503_ = v_target_2509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(lean_object* v_data_2513_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_nbuckets_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2514_ = lean_array_get_size(v_data_2513_);
v___x_2515_ = lean_unsigned_to_nat(2u);
v_nbuckets_2516_ = lean_nat_mul(v___x_2514_, v___x_2515_);
v___x_2517_ = lean_unsigned_to_nat(0u);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_mk_array(v_nbuckets_2516_, v___x_2518_);
v___x_2520_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v___x_2517_, v_data_2513_, v___x_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(lean_object* v_m_2521_, lean_object* v_a_2522_, lean_object* v_b_2523_){
_start:
{
lean_object* v_size_2524_; lean_object* v_buckets_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2568_; 
v_size_2524_ = lean_ctor_get(v_m_2521_, 0);
v_buckets_2525_ = lean_ctor_get(v_m_2521_, 1);
v_isSharedCheck_2568_ = !lean_is_exclusive(v_m_2521_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2527_ = v_m_2521_;
v_isShared_2528_ = v_isSharedCheck_2568_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_buckets_2525_);
lean_inc(v_size_2524_);
lean_dec(v_m_2521_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2568_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2529_; uint64_t v___x_2530_; uint64_t v___x_2531_; uint64_t v___x_2532_; uint64_t v_fold_2533_; uint64_t v___x_2534_; uint64_t v___x_2535_; uint64_t v___x_2536_; size_t v___x_2537_; size_t v___x_2538_; size_t v___x_2539_; size_t v___x_2540_; size_t v___x_2541_; lean_object* v_bkt_2542_; uint8_t v___x_2543_; 
v___x_2529_ = lean_array_get_size(v_buckets_2525_);
v___x_2530_ = l_Lean_ExprStructEq_hash(v_a_2522_);
v___x_2531_ = 32ULL;
v___x_2532_ = lean_uint64_shift_right(v___x_2530_, v___x_2531_);
v_fold_2533_ = lean_uint64_xor(v___x_2530_, v___x_2532_);
v___x_2534_ = 16ULL;
v___x_2535_ = lean_uint64_shift_right(v_fold_2533_, v___x_2534_);
v___x_2536_ = lean_uint64_xor(v_fold_2533_, v___x_2535_);
v___x_2537_ = lean_uint64_to_usize(v___x_2536_);
v___x_2538_ = lean_usize_of_nat(v___x_2529_);
v___x_2539_ = ((size_t)1ULL);
v___x_2540_ = lean_usize_sub(v___x_2538_, v___x_2539_);
v___x_2541_ = lean_usize_land(v___x_2537_, v___x_2540_);
v_bkt_2542_ = lean_array_uget_borrowed(v_buckets_2525_, v___x_2541_);
v___x_2543_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_2522_, v_bkt_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v_size_x27_2545_; lean_object* v___x_2546_; lean_object* v_buckets_x27_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2544_ = lean_unsigned_to_nat(1u);
v_size_x27_2545_ = lean_nat_add(v_size_2524_, v___x_2544_);
lean_dec(v_size_2524_);
lean_inc(v_bkt_2542_);
v___x_2546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2546_, 0, v_a_2522_);
lean_ctor_set(v___x_2546_, 1, v_b_2523_);
lean_ctor_set(v___x_2546_, 2, v_bkt_2542_);
v_buckets_x27_2547_ = lean_array_uset(v_buckets_2525_, v___x_2541_, v___x_2546_);
v___x_2548_ = lean_unsigned_to_nat(4u);
v___x_2549_ = lean_nat_mul(v_size_x27_2545_, v___x_2548_);
v___x_2550_ = lean_unsigned_to_nat(3u);
v___x_2551_ = lean_nat_div(v___x_2549_, v___x_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_array_get_size(v_buckets_x27_2547_);
v___x_2553_ = lean_nat_dec_le(v___x_2551_, v___x_2552_);
lean_dec(v___x_2551_);
if (v___x_2553_ == 0)
{
lean_object* v_val_2554_; lean_object* v___x_2556_; 
v_val_2554_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_buckets_x27_2547_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v_val_2554_);
lean_ctor_set(v___x_2527_, 0, v_size_x27_2545_);
v___x_2556_ = v___x_2527_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_size_x27_2545_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_val_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v___x_2559_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v_buckets_x27_2547_);
lean_ctor_set(v___x_2527_, 0, v_size_x27_2545_);
v___x_2559_ = v___x_2527_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_size_x27_2545_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_buckets_x27_2547_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
lean_object* v___x_2561_; lean_object* v_buckets_x27_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
lean_inc(v_bkt_2542_);
v___x_2561_ = lean_box(0);
v_buckets_x27_2562_ = lean_array_uset(v_buckets_2525_, v___x_2541_, v___x_2561_);
v___x_2563_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_2522_, v_b_2523_, v_bkt_2542_);
v___x_2564_ = lean_array_uset(v_buckets_x27_2562_, v___x_2541_, v___x_2563_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v___x_2564_);
v___x_2566_ = v___x_2527_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_size_2524_);
lean_ctor_set(v_reuseFailAlloc_2567_, 1, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(lean_object* v_a_2569_, lean_object* v_e_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2573_ = lean_st_ref_take(v_a_2569_);
v___x_2574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v___x_2573_, v_e_2570_, v_a_2571_);
v___x_2575_ = lean_st_ref_set(v_a_2569_, v___x_2574_);
v___x_2576_ = lean_box(0);
return v___x_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed(lean_object* v_a_2577_, lean_object* v_e_2578_, lean_object* v_a_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2(v_a_2577_, v_e_2578_, v_a_2579_);
lean_dec(v_a_2577_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(lean_object* v_fvars_2584_, lean_object* v_pre_2585_, lean_object* v_post_2586_, uint8_t v_usedLetOnly_2587_, uint8_t v_skipConstInApp_2588_, uint8_t v_skipInstances_2589_, lean_object* v_body_2590_, lean_object* v_x_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_array_push(v_fvars_2584_, v_x_2591_);
v___x_2599_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2585_, v_post_2586_, v_usedLetOnly_2587_, v_skipConstInApp_2588_, v_skipInstances_2589_, v___x_2598_, v_body_2590_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_2600_, lean_object* v_pre_2601_, lean_object* v_post_2602_, lean_object* v_usedLetOnly_2603_, lean_object* v_skipConstInApp_2604_, lean_object* v_skipInstances_2605_, lean_object* v_body_2606_, lean_object* v_x_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
uint8_t v_usedLetOnly_boxed_2614_; uint8_t v_skipConstInApp_boxed_2615_; uint8_t v_skipInstances_boxed_2616_; lean_object* v_res_2617_; 
v_usedLetOnly_boxed_2614_ = lean_unbox(v_usedLetOnly_2603_);
v_skipConstInApp_boxed_2615_ = lean_unbox(v_skipConstInApp_2604_);
v_skipInstances_boxed_2616_ = lean_unbox(v_skipInstances_2605_);
v_res_2617_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0(v_fvars_2600_, v_pre_2601_, v_post_2602_, v_usedLetOnly_boxed_2614_, v_skipConstInApp_boxed_2615_, v_skipInstances_boxed_2616_, v_body_2606_, v_x_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(lean_object* v_pre_2618_, lean_object* v_post_2619_, uint8_t v_usedLetOnly_2620_, uint8_t v_skipConstInApp_2621_, uint8_t v_skipInstances_2622_, lean_object* v_e_2623_, lean_object* v_a_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
lean_inc_ref(v_post_2619_);
lean_inc(v___y_2628_);
lean_inc_ref(v___y_2627_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc_ref(v_e_2623_);
v___x_2630_ = lean_apply_6(v_post_2619_, v_e_2623_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, lean_box(0));
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2649_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2649_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2649_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
switch(lean_obj_tag(v_a_2631_))
{
case 0:
{
lean_object* v_e_2635_; lean_object* v___x_2637_; 
lean_dec_ref(v_e_2623_);
lean_dec_ref(v_post_2619_);
lean_dec_ref(v_pre_2618_);
v_e_2635_ = lean_ctor_get(v_a_2631_, 0);
lean_inc_ref(v_e_2635_);
lean_dec_ref(v_a_2631_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_e_2635_);
v___x_2637_ = v___x_2633_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_e_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
case 1:
{
lean_object* v_e_2639_; lean_object* v___x_2640_; 
lean_del_object(v___x_2633_);
lean_dec_ref(v_e_2623_);
v_e_2639_ = lean_ctor_get(v_a_2631_, 0);
lean_inc_ref(v_e_2639_);
lean_dec_ref(v_a_2631_);
v___x_2640_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2618_, v_post_2619_, v_usedLetOnly_2620_, v_skipConstInApp_2621_, v_skipInstances_2622_, v_e_2639_, v_a_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2640_;
}
default: 
{
lean_object* v_e_x3f_2641_; 
lean_dec_ref(v_post_2619_);
lean_dec_ref(v_pre_2618_);
v_e_x3f_2641_ = lean_ctor_get(v_a_2631_, 0);
lean_inc(v_e_x3f_2641_);
lean_dec_ref(v_a_2631_);
if (lean_obj_tag(v_e_x3f_2641_) == 0)
{
lean_object* v___x_2643_; 
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_e_2623_);
v___x_2643_ = v___x_2633_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_e_2623_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
else
{
lean_object* v_val_2645_; lean_object* v___x_2647_; 
lean_dec_ref(v_e_2623_);
v_val_2645_ = lean_ctor_get(v_e_x3f_2641_, 0);
lean_inc(v_val_2645_);
lean_dec_ref(v_e_x3f_2641_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_val_2645_);
v___x_2647_ = v___x_2633_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_val_2645_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v_e_2623_);
lean_dec_ref(v_post_2619_);
lean_dec_ref(v_pre_2618_);
v_a_2650_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2630_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2630_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(lean_object* v_pre_2658_, lean_object* v_post_2659_, uint8_t v_usedLetOnly_2660_, uint8_t v_skipConstInApp_2661_, uint8_t v_skipInstances_2662_, lean_object* v_fvars_2663_, lean_object* v_e_2664_, lean_object* v_a_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
if (lean_obj_tag(v_e_2664_) == 6)
{
lean_object* v_binderName_2671_; lean_object* v_binderType_2672_; lean_object* v_body_2673_; uint8_t v_binderInfo_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_binderName_2671_ = lean_ctor_get(v_e_2664_, 0);
lean_inc(v_binderName_2671_);
v_binderType_2672_ = lean_ctor_get(v_e_2664_, 1);
lean_inc_ref(v_binderType_2672_);
v_body_2673_ = lean_ctor_get(v_e_2664_, 2);
lean_inc_ref(v_body_2673_);
v_binderInfo_2674_ = lean_ctor_get_uint8(v_e_2664_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_2664_);
v___x_2675_ = lean_expr_instantiate_rev(v_binderType_2672_, v_fvars_2663_);
lean_dec_ref(v_binderType_2672_);
lean_inc_ref(v_post_2659_);
lean_inc_ref(v_pre_2658_);
v___x_2676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2658_, v_post_2659_, v_usedLetOnly_2660_, v_skipConstInApp_2661_, v_skipInstances_2662_, v___x_2675_, v_a_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___f_2681_; uint8_t v___x_2682_; lean_object* v___x_2683_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = lean_box(v_usedLetOnly_2660_);
v___x_2679_ = lean_box(v_skipConstInApp_2661_);
v___x_2680_ = lean_box(v_skipInstances_2662_);
v___f_2681_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2681_, 0, v_fvars_2663_);
lean_closure_set(v___f_2681_, 1, v_pre_2658_);
lean_closure_set(v___f_2681_, 2, v_post_2659_);
lean_closure_set(v___f_2681_, 3, v___x_2678_);
lean_closure_set(v___f_2681_, 4, v___x_2679_);
lean_closure_set(v___f_2681_, 5, v___x_2680_);
lean_closure_set(v___f_2681_, 6, v_body_2673_);
v___x_2682_ = 0;
v___x_2683_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_2671_, v_binderInfo_2674_, v_a_2677_, v___f_2681_, v___x_2682_, v_a_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2683_;
}
else
{
lean_dec_ref(v_body_2673_);
lean_dec(v_binderName_2671_);
lean_dec_ref(v_fvars_2663_);
lean_dec_ref(v_post_2659_);
lean_dec_ref(v_pre_2658_);
return v___x_2676_;
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2684_ = lean_expr_instantiate_rev(v_e_2664_, v_fvars_2663_);
lean_dec_ref(v_e_2664_);
lean_inc_ref(v_post_2659_);
lean_inc_ref(v_pre_2658_);
v___x_2685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2658_, v_post_2659_, v_usedLetOnly_2660_, v_skipConstInApp_2661_, v_skipInstances_2662_, v___x_2684_, v_a_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; uint8_t v___x_2687_; uint8_t v___x_2688_; uint8_t v___x_2689_; lean_object* v___x_2690_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
lean_inc(v_a_2686_);
lean_dec_ref(v___x_2685_);
v___x_2687_ = 0;
v___x_2688_ = 1;
v___x_2689_ = 1;
v___x_2690_ = l_Lean_Meta_mkLambdaFVars(v_fvars_2663_, v_a_2686_, v___x_2687_, v_usedLetOnly_2660_, v___x_2687_, v___x_2688_, v___x_2689_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec_ref(v_fvars_2663_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
v___x_2692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2658_, v_post_2659_, v_usedLetOnly_2660_, v_skipConstInApp_2661_, v_skipInstances_2662_, v_a_2691_, v_a_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2692_;
}
else
{
lean_dec_ref(v_post_2659_);
lean_dec_ref(v_pre_2658_);
return v___x_2690_;
}
}
else
{
lean_dec_ref(v_fvars_2663_);
lean_dec_ref(v_post_2659_);
lean_dec_ref(v_pre_2658_);
return v___x_2685_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(lean_object* v_fvars_2693_, lean_object* v_pre_2694_, lean_object* v_post_2695_, uint8_t v_usedLetOnly_2696_, uint8_t v_skipConstInApp_2697_, uint8_t v_skipInstances_2698_, lean_object* v_body_2699_, lean_object* v_x_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_array_push(v_fvars_2693_, v_x_2700_);
v___x_2708_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2694_, v_post_2695_, v_usedLetOnly_2696_, v_skipConstInApp_2697_, v_skipInstances_2698_, v___x_2707_, v_body_2699_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed(lean_object* v_fvars_2709_, lean_object* v_pre_2710_, lean_object* v_post_2711_, lean_object* v_usedLetOnly_2712_, lean_object* v_skipConstInApp_2713_, lean_object* v_skipInstances_2714_, lean_object* v_body_2715_, lean_object* v_x_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v_usedLetOnly_boxed_2723_; uint8_t v_skipConstInApp_boxed_2724_; uint8_t v_skipInstances_boxed_2725_; lean_object* v_res_2726_; 
v_usedLetOnly_boxed_2723_ = lean_unbox(v_usedLetOnly_2712_);
v_skipConstInApp_boxed_2724_ = lean_unbox(v_skipConstInApp_2713_);
v_skipInstances_boxed_2725_ = lean_unbox(v_skipInstances_2714_);
v_res_2726_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0(v_fvars_2709_, v_pre_2710_, v_post_2711_, v_usedLetOnly_boxed_2723_, v_skipConstInApp_boxed_2724_, v_skipInstances_boxed_2725_, v_body_2715_, v_x_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(lean_object* v_pre_2727_, lean_object* v_post_2728_, uint8_t v_usedLetOnly_2729_, uint8_t v_skipConstInApp_2730_, uint8_t v_skipInstances_2731_, lean_object* v_fvars_2732_, lean_object* v_e_2733_, lean_object* v_a_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
if (lean_obj_tag(v_e_2733_) == 8)
{
lean_object* v_declName_2740_; lean_object* v_type_2741_; lean_object* v_value_2742_; lean_object* v_body_2743_; uint8_t v_nondep_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v_declName_2740_ = lean_ctor_get(v_e_2733_, 0);
lean_inc(v_declName_2740_);
v_type_2741_ = lean_ctor_get(v_e_2733_, 1);
lean_inc_ref(v_type_2741_);
v_value_2742_ = lean_ctor_get(v_e_2733_, 2);
lean_inc_ref(v_value_2742_);
v_body_2743_ = lean_ctor_get(v_e_2733_, 3);
lean_inc_ref(v_body_2743_);
v_nondep_2744_ = lean_ctor_get_uint8(v_e_2733_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_2733_);
v___x_2745_ = lean_expr_instantiate_rev(v_type_2741_, v_fvars_2732_);
lean_dec_ref(v_type_2741_);
lean_inc_ref(v_post_2728_);
lean_inc_ref(v_pre_2727_);
v___x_2746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2727_, v_post_2728_, v_usedLetOnly_2729_, v_skipConstInApp_2730_, v_skipInstances_2731_, v___x_2745_, v_a_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
v___x_2748_ = lean_expr_instantiate_rev(v_value_2742_, v_fvars_2732_);
lean_dec_ref(v_value_2742_);
lean_inc_ref(v_post_2728_);
lean_inc_ref(v_pre_2727_);
v___x_2749_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2727_, v_post_2728_, v_usedLetOnly_2729_, v_skipConstInApp_2730_, v_skipInstances_2731_, v___x_2748_, v_a_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___f_2754_; uint8_t v___x_2755_; lean_object* v___x_2756_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
v___x_2751_ = lean_box(v_usedLetOnly_2729_);
v___x_2752_ = lean_box(v_skipConstInApp_2730_);
v___x_2753_ = lean_box(v_skipInstances_2731_);
v___f_2754_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___lam__0___boxed), 14, 7);
lean_closure_set(v___f_2754_, 0, v_fvars_2732_);
lean_closure_set(v___f_2754_, 1, v_pre_2727_);
lean_closure_set(v___f_2754_, 2, v_post_2728_);
lean_closure_set(v___f_2754_, 3, v___x_2751_);
lean_closure_set(v___f_2754_, 4, v___x_2752_);
lean_closure_set(v___f_2754_, 5, v___x_2753_);
lean_closure_set(v___f_2754_, 6, v_body_2743_);
v___x_2755_ = 0;
v___x_2756_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_declName_2740_, v_a_2747_, v_a_2750_, v___f_2754_, v_nondep_2744_, v___x_2755_, v_a_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2756_;
}
else
{
lean_dec(v_a_2747_);
lean_dec_ref(v_body_2743_);
lean_dec(v_declName_2740_);
lean_dec_ref(v_fvars_2732_);
lean_dec_ref(v_post_2728_);
lean_dec_ref(v_pre_2727_);
return v___x_2749_;
}
}
else
{
lean_dec_ref(v_body_2743_);
lean_dec_ref(v_value_2742_);
lean_dec(v_declName_2740_);
lean_dec_ref(v_fvars_2732_);
lean_dec_ref(v_post_2728_);
lean_dec_ref(v_pre_2727_);
return v___x_2746_;
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_expr_instantiate_rev(v_e_2733_, v_fvars_2732_);
lean_dec_ref(v_e_2733_);
lean_inc_ref(v_post_2728_);
lean_inc_ref(v_pre_2727_);
v___x_2758_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2727_, v_post_2728_, v_usedLetOnly_2729_, v_skipConstInApp_2730_, v_skipInstances_2731_, v___x_2757_, v_a_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; uint8_t v___x_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref(v___x_2758_);
v___x_2760_ = 0;
v___x_2761_ = 1;
v___x_2762_ = l_Lean_Meta_mkLetFVars(v_fvars_2732_, v_a_2759_, v_usedLetOnly_2729_, v___x_2760_, v___x_2761_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
lean_dec_ref(v_fvars_2732_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2727_, v_post_2728_, v_usedLetOnly_2729_, v_skipConstInApp_2730_, v_skipInstances_2731_, v_a_2763_, v_a_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
return v___x_2764_;
}
else
{
lean_dec_ref(v_post_2728_);
lean_dec_ref(v_pre_2727_);
return v___x_2762_;
}
}
else
{
lean_dec_ref(v_fvars_2732_);
lean_dec_ref(v_post_2728_);
lean_dec_ref(v_pre_2727_);
return v___x_2758_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(lean_object* v_pre_2765_, lean_object* v_post_2766_, uint8_t v_usedLetOnly_2767_, uint8_t v_skipConstInApp_2768_, uint8_t v_skipInstances_2769_, size_t v_sz_2770_, size_t v_i_2771_, lean_object* v_bs_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
uint8_t v___x_2779_; 
v___x_2779_ = lean_usize_dec_lt(v_i_2771_, v_sz_2770_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
lean_dec_ref(v_post_2766_);
lean_dec_ref(v_pre_2765_);
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_bs_2772_);
return v___x_2780_;
}
else
{
lean_object* v_v_2781_; lean_object* v___x_2782_; 
v_v_2781_ = lean_array_uget_borrowed(v_bs_2772_, v_i_2771_);
lean_inc(v_v_2781_);
lean_inc_ref(v_post_2766_);
lean_inc_ref(v_pre_2765_);
v___x_2782_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2765_, v_post_2766_, v_usedLetOnly_2767_, v_skipConstInApp_2768_, v_skipInstances_2769_, v_v_2781_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v_bs_x27_2785_; size_t v___x_2786_; size_t v___x_2787_; lean_object* v___x_2788_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref(v___x_2782_);
v___x_2784_ = lean_unsigned_to_nat(0u);
v_bs_x27_2785_ = lean_array_uset(v_bs_2772_, v_i_2771_, v___x_2784_);
v___x_2786_ = ((size_t)1ULL);
v___x_2787_ = lean_usize_add(v_i_2771_, v___x_2786_);
v___x_2788_ = lean_array_uset(v_bs_x27_2785_, v_i_2771_, v_a_2783_);
v_i_2771_ = v___x_2787_;
v_bs_2772_ = v___x_2788_;
goto _start;
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v_bs_2772_);
lean_dec_ref(v_post_2766_);
lean_dec_ref(v_pre_2765_);
v_a_2790_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2782_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2782_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_2798_, lean_object* v_post_2799_, uint8_t v_usedLetOnly_2800_, uint8_t v_skipConstInApp_2801_, uint8_t v_skipInstances_2802_, lean_object* v___x_2803_, lean_object* v___y_2804_, lean_object* v_b_2805_, lean_object* v_a_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2798_, v_post_2799_, v_usedLetOnly_2800_, v_skipConstInApp_2801_, v_skipInstances_2802_, v___x_2803_, v___y_2804_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2822_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2815_ = v___x_2812_;
v_isShared_2816_ = v_isSharedCheck_2822_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2812_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2822_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2820_; 
v___x_2817_ = lean_array_fset(v_b_2805_, v_a_2806_, v_a_2813_);
v___x_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2818_);
v___x_2820_ = v___x_2815_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v_b_2805_);
v_a_2823_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2812_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2812_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_2831_, lean_object* v_post_2832_, lean_object* v_usedLetOnly_2833_, lean_object* v_skipConstInApp_2834_, lean_object* v_skipInstances_2835_, lean_object* v___x_2836_, lean_object* v___y_2837_, lean_object* v_b_2838_, lean_object* v_a_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
uint8_t v_usedLetOnly_boxed_2845_; uint8_t v_skipConstInApp_boxed_2846_; uint8_t v_skipInstances_boxed_2847_; lean_object* v_res_2848_; 
v_usedLetOnly_boxed_2845_ = lean_unbox(v_usedLetOnly_2833_);
v_skipConstInApp_boxed_2846_ = lean_unbox(v_skipConstInApp_2834_);
v_skipInstances_boxed_2847_ = lean_unbox(v_skipInstances_2835_);
v_res_2848_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0(v_pre_2831_, v_post_2832_, v_usedLetOnly_boxed_2845_, v_skipConstInApp_boxed_2846_, v_skipInstances_boxed_2847_, v___x_2836_, v___y_2837_, v_b_2838_, v_a_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v_a_2839_);
lean_dec(v___y_2837_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(lean_object* v_upperBound_2849_, lean_object* v___x_2850_, lean_object* v_pre_2851_, lean_object* v_post_2852_, uint8_t v_usedLetOnly_2853_, uint8_t v_skipConstInApp_2854_, uint8_t v_skipInstances_2855_, lean_object* v_a_2856_, lean_object* v_b_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___y_2865_; uint8_t v___x_2888_; 
v___x_2888_ = lean_nat_dec_lt(v_a_2856_, v_upperBound_2849_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2889_; 
lean_dec(v_a_2856_);
lean_dec_ref(v_post_2852_);
lean_dec_ref(v_pre_2851_);
v___x_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2889_, 0, v_b_2857_);
return v___x_2889_;
}
else
{
lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v___x_2890_ = lean_array_fget_borrowed(v_b_2857_, v_a_2856_);
v___x_2891_ = lean_array_get_size(v___x_2850_);
v___x_2892_ = lean_nat_dec_lt(v_a_2856_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___f_2896_; 
lean_inc(v___x_2890_);
v___x_2893_ = lean_box(v_usedLetOnly_2853_);
v___x_2894_ = lean_box(v_skipConstInApp_2854_);
v___x_2895_ = lean_box(v_skipInstances_2855_);
lean_inc(v_a_2856_);
lean_inc(v___y_2858_);
lean_inc_ref(v_post_2852_);
lean_inc_ref(v_pre_2851_);
v___f_2896_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2896_, 0, v_pre_2851_);
lean_closure_set(v___f_2896_, 1, v_post_2852_);
lean_closure_set(v___f_2896_, 2, v___x_2893_);
lean_closure_set(v___f_2896_, 3, v___x_2894_);
lean_closure_set(v___f_2896_, 4, v___x_2895_);
lean_closure_set(v___f_2896_, 5, v___x_2890_);
lean_closure_set(v___f_2896_, 6, v___y_2858_);
lean_closure_set(v___f_2896_, 7, v_b_2857_);
lean_closure_set(v___f_2896_, 8, v_a_2856_);
v___y_2865_ = v___f_2896_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2897_; uint8_t v_isInstance_2898_; 
v___x_2897_ = lean_array_fget_borrowed(v___x_2850_, v_a_2856_);
v_isInstance_2898_ = lean_ctor_get_uint8(v___x_2897_, sizeof(void*)*1 + 4);
if (v_isInstance_2898_ == 0)
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___f_2902_; 
lean_inc(v___x_2890_);
v___x_2899_ = lean_box(v_usedLetOnly_2853_);
v___x_2900_ = lean_box(v_skipConstInApp_2854_);
v___x_2901_ = lean_box(v_skipInstances_2855_);
lean_inc(v_a_2856_);
lean_inc(v___y_2858_);
lean_inc_ref(v_post_2852_);
lean_inc_ref(v_pre_2851_);
v___f_2902_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_2902_, 0, v_pre_2851_);
lean_closure_set(v___f_2902_, 1, v_post_2852_);
lean_closure_set(v___f_2902_, 2, v___x_2899_);
lean_closure_set(v___f_2902_, 3, v___x_2900_);
lean_closure_set(v___f_2902_, 4, v___x_2901_);
lean_closure_set(v___f_2902_, 5, v___x_2890_);
lean_closure_set(v___f_2902_, 6, v___y_2858_);
lean_closure_set(v___f_2902_, 7, v_b_2857_);
lean_closure_set(v___f_2902_, 8, v_a_2856_);
v___y_2865_ = v___f_2902_;
goto v___jp_2864_;
}
else
{
lean_object* v___x_2903_; lean_object* v___f_2904_; 
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_b_2857_);
v___f_2904_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_2904_, 0, v___x_2903_);
v___y_2865_ = v___f_2904_;
goto v___jp_2864_;
}
}
}
v___jp_2864_:
{
lean_object* v___x_2866_; 
lean_inc(v___y_2862_);
lean_inc_ref(v___y_2861_);
lean_inc(v___y_2860_);
lean_inc_ref(v___y_2859_);
v___x_2866_ = lean_apply_5(v___y_2865_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, lean_box(0));
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2879_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2879_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2879_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
if (lean_obj_tag(v_a_2867_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2873_; 
lean_dec(v_a_2856_);
lean_dec_ref(v_post_2852_);
lean_dec_ref(v_pre_2851_);
v_a_2871_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_a_2871_);
lean_dec_ref(v_a_2867_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v_a_2871_);
v___x_2873_ = v___x_2869_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
lean_del_object(v___x_2869_);
v_a_2875_ = lean_ctor_get(v_a_2867_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v_a_2867_);
v___x_2876_ = lean_unsigned_to_nat(1u);
v___x_2877_ = lean_nat_add(v_a_2856_, v___x_2876_);
lean_dec(v_a_2856_);
v_a_2856_ = v___x_2877_;
v_b_2857_ = v_a_2875_;
goto _start;
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec(v_a_2856_);
lean_dec_ref(v_post_2852_);
lean_dec_ref(v_pre_2851_);
v_a_2880_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2866_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2866_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(uint8_t v_skipInstances_2905_, lean_object* v_pre_2906_, lean_object* v_post_2907_, uint8_t v_usedLetOnly_2908_, uint8_t v_skipConstInApp_2909_, lean_object* v_x_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_f_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; 
if (lean_obj_tag(v_x_2910_) == 5)
{
lean_object* v_fn_2968_; lean_object* v_arg_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v_fn_2968_ = lean_ctor_get(v_x_2910_, 0);
lean_inc_ref(v_fn_2968_);
v_arg_2969_ = lean_ctor_get(v_x_2910_, 1);
lean_inc_ref(v_arg_2969_);
lean_dec_ref(v_x_2910_);
v___x_2970_ = lean_array_set(v_x_2911_, v_x_2912_, v_arg_2969_);
v___x_2971_ = lean_unsigned_to_nat(1u);
v___x_2972_ = lean_nat_sub(v_x_2912_, v___x_2971_);
lean_dec(v_x_2912_);
v_x_2910_ = v_fn_2968_;
v_x_2911_ = v___x_2970_;
v_x_2912_ = v___x_2972_;
goto _start;
}
else
{
lean_dec(v_x_2912_);
if (v_skipConstInApp_2909_ == 0)
{
goto v___jp_2965_;
}
else
{
uint8_t v___x_2974_; 
v___x_2974_ = l_Lean_Expr_isConst(v_x_2910_);
if (v___x_2974_ == 0)
{
goto v___jp_2965_;
}
else
{
v_f_2920_ = v_x_2910_;
v___y_2921_ = v___y_2913_;
v___y_2922_ = v___y_2914_;
v___y_2923_ = v___y_2915_;
v___y_2924_ = v___y_2916_;
v___y_2925_ = v___y_2917_;
goto v___jp_2919_;
}
}
}
v___jp_2919_:
{
if (v_skipInstances_2905_ == 0)
{
size_t v_sz_2926_; size_t v___x_2927_; lean_object* v___x_2928_; 
v_sz_2926_ = lean_array_size(v_x_2911_);
v___x_2927_ = ((size_t)0ULL);
lean_inc_ref(v_post_2907_);
lean_inc_ref(v_pre_2906_);
v___x_2928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_2906_, v_post_2907_, v_usedLetOnly_2908_, v_skipConstInApp_2909_, v_skipInstances_2905_, v_sz_2926_, v___x_2927_, v_x_2911_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref(v___x_2928_);
v___x_2930_ = l_Lean_mkAppN(v_f_2920_, v_a_2929_);
lean_dec(v_a_2929_);
v___x_2931_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2906_, v_post_2907_, v_usedLetOnly_2908_, v_skipConstInApp_2909_, v_skipInstances_2905_, v___x_2930_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2931_;
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec_ref(v_f_2920_);
lean_dec_ref(v_post_2907_);
lean_dec_ref(v_pre_2906_);
v_a_2932_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2928_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2928_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
else
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_array_get_size(v_x_2911_);
lean_inc_ref(v_f_2920_);
v___x_2941_ = l_Lean_Meta_getFunInfoNArgs(v_f_2920_, v___x_2940_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v_paramInfo_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v_paramInfo_2943_ = lean_ctor_get(v_a_2942_, 0);
lean_inc_ref(v_paramInfo_2943_);
lean_dec(v_a_2942_);
v___x_2944_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_2907_);
lean_inc_ref(v_pre_2906_);
v___x_2945_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v___x_2940_, v_paramInfo_2943_, v_pre_2906_, v_post_2907_, v_usedLetOnly_2908_, v_skipConstInApp_2909_, v_skipInstances_2905_, v___x_2944_, v_x_2911_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec_ref(v_paramInfo_2943_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = l_Lean_mkAppN(v_f_2920_, v_a_2946_);
lean_dec(v_a_2946_);
v___x_2948_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2906_, v_post_2907_, v_usedLetOnly_2908_, v_skipConstInApp_2909_, v_skipInstances_2905_, v___x_2947_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2948_;
}
else
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_f_2920_);
lean_dec_ref(v_post_2907_);
lean_dec_ref(v_pre_2906_);
v_a_2949_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2945_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2945_);
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
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec_ref(v_f_2920_);
lean_dec_ref(v_x_2911_);
lean_dec_ref(v_post_2907_);
lean_dec_ref(v_pre_2906_);
v_a_2957_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2941_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2941_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
v___jp_2965_:
{
lean_object* v___x_2966_; 
lean_inc_ref(v_post_2907_);
lean_inc_ref(v_pre_2906_);
v___x_2966_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2906_, v_post_2907_, v_usedLetOnly_2908_, v_skipConstInApp_2909_, v_skipInstances_2905_, v_x_2910_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref(v___x_2966_);
v_f_2920_ = v_a_2967_;
v___y_2921_ = v___y_2913_;
v___y_2922_ = v___y_2914_;
v___y_2923_ = v___y_2915_;
v___y_2924_ = v___y_2916_;
v___y_2925_ = v___y_2917_;
goto v___jp_2919_;
}
else
{
lean_dec_ref(v_x_2911_);
lean_dec_ref(v_post_2907_);
lean_dec_ref(v_pre_2906_);
return v___x_2966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(lean_object* v_pre_2975_, lean_object* v_e_2976_, lean_object* v_post_2977_, uint8_t v_usedLetOnly_2978_, uint8_t v_skipConstInApp_2979_, uint8_t v_skipInstances_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; 
lean_inc_ref(v_pre_2975_);
lean_inc(v___y_2985_);
lean_inc_ref(v___y_2984_);
lean_inc(v___y_2983_);
lean_inc_ref(v___y_2982_);
lean_inc_ref(v_e_2976_);
v___x_2987_ = lean_apply_6(v_pre_2975_, v_e_2976_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, lean_box(0));
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3036_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_2990_ = v___x_2987_;
v_isShared_2991_ = v_isSharedCheck_3036_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2987_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3036_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___y_2993_; 
switch(lean_obj_tag(v_a_2988_))
{
case 0:
{
lean_object* v_e_3028_; lean_object* v___x_3030_; 
lean_dec_ref(v_post_2977_);
lean_dec_ref(v_e_2976_);
lean_dec_ref(v_pre_2975_);
v_e_3028_ = lean_ctor_get(v_a_2988_, 0);
lean_inc_ref(v_e_3028_);
lean_dec_ref(v_a_2988_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 0, v_e_3028_);
v___x_3030_ = v___x_2990_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_e_3028_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
case 1:
{
lean_object* v_e_3032_; lean_object* v___x_3033_; 
lean_del_object(v___x_2990_);
lean_dec_ref(v_e_2976_);
v_e_3032_ = lean_ctor_get(v_a_2988_, 0);
lean_inc_ref(v_e_3032_);
lean_dec_ref(v_a_2988_);
v___x_3033_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v_e_3032_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_3033_;
}
default: 
{
lean_object* v_e_x3f_3034_; 
lean_del_object(v___x_2990_);
v_e_x3f_3034_ = lean_ctor_get(v_a_2988_, 0);
lean_inc(v_e_x3f_3034_);
lean_dec_ref(v_a_2988_);
if (lean_obj_tag(v_e_x3f_3034_) == 0)
{
v___y_2993_ = v_e_2976_;
goto v___jp_2992_;
}
else
{
lean_object* v_val_3035_; 
lean_dec_ref(v_e_2976_);
v_val_3035_ = lean_ctor_get(v_e_x3f_3034_, 0);
lean_inc(v_val_3035_);
lean_dec_ref(v_e_x3f_3034_);
v___y_2993_ = v_val_3035_;
goto v___jp_2992_;
}
}
}
v___jp_2992_:
{
switch(lean_obj_tag(v___y_2993_))
{
case 7:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2995_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___x_2994_, v___y_2993_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2995_;
}
case 6:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2997_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___x_2996_, v___y_2993_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2997_;
}
case 8:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___closed__0));
v___x_2999_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___x_2998_, v___y_2993_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2999_;
}
case 5:
{
lean_object* v_dummy_3000_; lean_object* v_nargs_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; 
v_dummy_3000_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3001_ = l_Lean_Expr_getAppNumArgs(v___y_2993_);
lean_inc(v_nargs_3001_);
v___x_3002_ = lean_mk_array(v_nargs_3001_, v_dummy_3000_);
v___x_3003_ = lean_unsigned_to_nat(1u);
v___x_3004_ = lean_nat_sub(v_nargs_3001_, v___x_3003_);
lean_dec(v_nargs_3001_);
v___x_3005_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_2980_, v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v___y_2993_, v___x_3002_, v___x_3004_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_3005_;
}
case 10:
{
lean_object* v_data_3006_; lean_object* v_expr_3007_; lean_object* v___x_3008_; 
v_data_3006_ = lean_ctor_get(v___y_2993_, 0);
v_expr_3007_ = lean_ctor_get(v___y_2993_, 1);
lean_inc_ref(v_expr_3007_);
lean_inc_ref(v_post_2977_);
lean_inc_ref(v_pre_2975_);
v___x_3008_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v_expr_3007_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v_a_3009_; size_t v___x_3010_; size_t v___x_3011_; uint8_t v___x_3012_; 
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref(v___x_3008_);
v___x_3010_ = lean_ptr_addr(v_expr_3007_);
v___x_3011_ = lean_ptr_addr(v_a_3009_);
v___x_3012_ = lean_usize_dec_eq(v___x_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_inc(v_data_3006_);
lean_dec_ref(v___y_2993_);
v___x_3013_ = l_Lean_Expr_mdata___override(v_data_3006_, v_a_3009_);
v___x_3014_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___x_3013_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; 
lean_dec(v_a_3009_);
v___x_3015_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___y_2993_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_3015_;
}
}
else
{
lean_dec_ref(v___y_2993_);
lean_dec_ref(v_post_2977_);
lean_dec_ref(v_pre_2975_);
return v___x_3008_;
}
}
case 11:
{
lean_object* v_typeName_3016_; lean_object* v_idx_3017_; lean_object* v_struct_3018_; lean_object* v___x_3019_; 
v_typeName_3016_ = lean_ctor_get(v___y_2993_, 0);
v_idx_3017_ = lean_ctor_get(v___y_2993_, 1);
v_struct_3018_ = lean_ctor_get(v___y_2993_, 2);
lean_inc_ref(v_struct_3018_);
lean_inc_ref(v_post_2977_);
lean_inc_ref(v_pre_2975_);
v___x_3019_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v_struct_3018_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; size_t v___x_3021_; size_t v___x_3022_; uint8_t v___x_3023_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = lean_ptr_addr(v_struct_3018_);
v___x_3022_ = lean_ptr_addr(v_a_3020_);
v___x_3023_ = lean_usize_dec_eq(v___x_3021_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_inc(v_idx_3017_);
lean_inc(v_typeName_3016_);
lean_dec_ref(v___y_2993_);
v___x_3024_ = l_Lean_Expr_proj___override(v_typeName_3016_, v_idx_3017_, v_a_3020_);
v___x_3025_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___x_3024_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_3025_;
}
else
{
lean_object* v___x_3026_; 
lean_dec(v_a_3020_);
v___x_3026_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___y_2993_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_3026_;
}
}
else
{
lean_dec_ref(v___y_2993_);
lean_dec_ref(v_post_2977_);
lean_dec_ref(v_pre_2975_);
return v___x_3019_;
}
}
default: 
{
lean_object* v___x_3027_; 
v___x_3027_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_2975_, v_post_2977_, v_usedLetOnly_2978_, v_skipConstInApp_2979_, v_skipInstances_2980_, v___y_2993_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_3027_;
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v_post_2977_);
lean_dec_ref(v_e_2976_);
lean_dec_ref(v_pre_2975_);
v_a_3037_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_2987_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_2987_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed(lean_object* v_pre_3045_, lean_object* v_e_3046_, lean_object* v_post_3047_, lean_object* v_usedLetOnly_3048_, lean_object* v_skipConstInApp_3049_, lean_object* v_skipInstances_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_){
_start:
{
uint8_t v_usedLetOnly_boxed_3057_; uint8_t v_skipConstInApp_boxed_3058_; uint8_t v_skipInstances_boxed_3059_; lean_object* v_res_3060_; 
v_usedLetOnly_boxed_3057_ = lean_unbox(v_usedLetOnly_3048_);
v_skipConstInApp_boxed_3058_ = lean_unbox(v_skipConstInApp_3049_);
v_skipInstances_boxed_3059_ = lean_unbox(v_skipInstances_3050_);
v_res_3060_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1(v_pre_3045_, v_e_3046_, v_post_3047_, v_usedLetOnly_boxed_3057_, v_skipConstInApp_boxed_3058_, v_skipInstances_boxed_3059_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_);
lean_dec(v___y_3055_);
lean_dec_ref(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(lean_object* v_pre_3061_, lean_object* v_post_3062_, uint8_t v_usedLetOnly_3063_, uint8_t v_skipConstInApp_3064_, uint8_t v_skipInstances_3065_, lean_object* v_e_3066_, lean_object* v_a_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_inc(v_a_3067_);
v___x_3073_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3073_, 0, lean_box(0));
lean_closure_set(v___x_3073_, 1, lean_box(0));
lean_closure_set(v___x_3073_, 2, v_a_3067_);
v___x_3074_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3073_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3108_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3108_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3108_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3079_; 
v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3075_, v_e_3066_);
lean_dec(v_a_3075_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___f_3083_; lean_object* v___x_3084_; 
lean_del_object(v___x_3077_);
v___x_3080_ = lean_box(v_usedLetOnly_3063_);
v___x_3081_ = lean_box(v_skipConstInApp_3064_);
v___x_3082_ = lean_box(v_skipInstances_3065_);
lean_inc_ref(v_e_3066_);
v___f_3083_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3083_, 0, v_pre_3061_);
lean_closure_set(v___f_3083_, 1, v_e_3066_);
lean_closure_set(v___f_3083_, 2, v_post_3062_);
lean_closure_set(v___f_3083_, 3, v___x_3080_);
lean_closure_set(v___f_3083_, 4, v___x_3081_);
lean_closure_set(v___f_3083_, 5, v___x_3082_);
v___x_3084_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v___f_3083_, v_a_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc_n(v_a_3085_, 2);
lean_dec_ref(v___x_3084_);
lean_inc(v_a_3067_);
v___f_3086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3086_, 0, v_a_3067_);
lean_closure_set(v___f_3086_, 1, v_e_3066_);
lean_closure_set(v___f_3086_, 2, v_a_3085_);
v___x_3087_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_3086_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3094_ == 0)
{
lean_object* v_unused_3095_; 
v_unused_3095_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3095_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v_a_3085_);
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3085_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3085_);
v_a_3096_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3087_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3087_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_dec_ref(v_e_3066_);
return v___x_3084_;
}
}
else
{
lean_object* v_val_3104_; lean_object* v___x_3106_; 
lean_dec_ref(v_e_3066_);
lean_dec_ref(v_post_3062_);
lean_dec_ref(v_pre_3061_);
v_val_3104_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_val_3104_);
lean_dec_ref(v___x_3079_);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v_val_3104_);
v___x_3106_ = v___x_3077_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_val_3104_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v_e_3066_);
lean_dec_ref(v_post_3062_);
lean_dec_ref(v_pre_3061_);
v_a_3109_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_3074_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3074_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_3117_, lean_object* v_pre_3118_, lean_object* v_post_3119_, lean_object* v_usedLetOnly_3120_, lean_object* v_skipConstInApp_3121_, lean_object* v_skipInstances_3122_, lean_object* v_body_3123_, lean_object* v_x_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
uint8_t v_usedLetOnly_boxed_3131_; uint8_t v_skipConstInApp_boxed_3132_; uint8_t v_skipInstances_boxed_3133_; lean_object* v_res_3134_; 
v_usedLetOnly_boxed_3131_ = lean_unbox(v_usedLetOnly_3120_);
v_skipConstInApp_boxed_3132_ = lean_unbox(v_skipConstInApp_3121_);
v_skipInstances_boxed_3133_ = lean_unbox(v_skipInstances_3122_);
v_res_3134_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(v_fvars_3117_, v_pre_3118_, v_post_3119_, v_usedLetOnly_boxed_3131_, v_skipConstInApp_boxed_3132_, v_skipInstances_boxed_3133_, v_body_3123_, v_x_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(lean_object* v_pre_3135_, lean_object* v_post_3136_, uint8_t v_usedLetOnly_3137_, uint8_t v_skipConstInApp_3138_, uint8_t v_skipInstances_3139_, lean_object* v_fvars_3140_, lean_object* v_e_3141_, lean_object* v_a_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
if (lean_obj_tag(v_e_3141_) == 7)
{
lean_object* v_binderName_3148_; lean_object* v_binderType_3149_; lean_object* v_body_3150_; uint8_t v_binderInfo_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_binderName_3148_ = lean_ctor_get(v_e_3141_, 0);
lean_inc(v_binderName_3148_);
v_binderType_3149_ = lean_ctor_get(v_e_3141_, 1);
lean_inc_ref(v_binderType_3149_);
v_body_3150_ = lean_ctor_get(v_e_3141_, 2);
lean_inc_ref(v_body_3150_);
v_binderInfo_3151_ = lean_ctor_get_uint8(v_e_3141_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3141_);
v___x_3152_ = lean_expr_instantiate_rev(v_binderType_3149_, v_fvars_3140_);
lean_dec_ref(v_binderType_3149_);
lean_inc_ref(v_post_3136_);
lean_inc_ref(v_pre_3135_);
v___x_3153_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3135_, v_post_3136_, v_usedLetOnly_3137_, v_skipConstInApp_3138_, v_skipInstances_3139_, v___x_3152_, v_a_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___f_3158_; uint8_t v___x_3159_; lean_object* v___x_3160_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref(v___x_3153_);
v___x_3155_ = lean_box(v_usedLetOnly_3137_);
v___x_3156_ = lean_box(v_skipConstInApp_3138_);
v___x_3157_ = lean_box(v_skipInstances_3139_);
v___f_3158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3158_, 0, v_fvars_3140_);
lean_closure_set(v___f_3158_, 1, v_pre_3135_);
lean_closure_set(v___f_3158_, 2, v_post_3136_);
lean_closure_set(v___f_3158_, 3, v___x_3155_);
lean_closure_set(v___f_3158_, 4, v___x_3156_);
lean_closure_set(v___f_3158_, 5, v___x_3157_);
lean_closure_set(v___f_3158_, 6, v_body_3150_);
v___x_3159_ = 0;
v___x_3160_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_binderName_3148_, v_binderInfo_3151_, v_a_3154_, v___f_3158_, v___x_3159_, v_a_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3160_;
}
else
{
lean_dec_ref(v_body_3150_);
lean_dec(v_binderName_3148_);
lean_dec_ref(v_fvars_3140_);
lean_dec_ref(v_post_3136_);
lean_dec_ref(v_pre_3135_);
return v___x_3153_;
}
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_expr_instantiate_rev(v_e_3141_, v_fvars_3140_);
lean_dec_ref(v_e_3141_);
lean_inc_ref(v_post_3136_);
lean_inc_ref(v_pre_3135_);
v___x_3162_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3135_, v_post_3136_, v_usedLetOnly_3137_, v_skipConstInApp_3138_, v_skipInstances_3139_, v___x_3161_, v_a_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; uint8_t v___x_3164_; uint8_t v___x_3165_; uint8_t v___x_3166_; lean_object* v___x_3167_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref(v___x_3162_);
v___x_3164_ = 0;
v___x_3165_ = 1;
v___x_3166_ = 1;
v___x_3167_ = l_Lean_Meta_mkForallFVars(v_fvars_3140_, v_a_3163_, v___x_3164_, v_usedLetOnly_3137_, v___x_3165_, v___x_3166_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec_ref(v_fvars_3140_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref(v___x_3167_);
v___x_3169_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3135_, v_post_3136_, v_usedLetOnly_3137_, v_skipConstInApp_3138_, v_skipInstances_3139_, v_a_3168_, v_a_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3169_;
}
else
{
lean_dec_ref(v_post_3136_);
lean_dec_ref(v_pre_3135_);
return v___x_3167_;
}
}
else
{
lean_dec_ref(v_fvars_3140_);
lean_dec_ref(v_post_3136_);
lean_dec_ref(v_pre_3135_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___lam__0(lean_object* v_fvars_3170_, lean_object* v_pre_3171_, lean_object* v_post_3172_, uint8_t v_usedLetOnly_3173_, uint8_t v_skipConstInApp_3174_, uint8_t v_skipInstances_3175_, lean_object* v_body_3176_, lean_object* v_x_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_array_push(v_fvars_3170_, v_x_3177_);
v___x_3185_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3171_, v_post_3172_, v_usedLetOnly_3173_, v_skipConstInApp_3174_, v_skipInstances_3175_, v___x_3184_, v_body_3176_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5___boxed(lean_object* v_pre_3186_, lean_object* v_post_3187_, lean_object* v_usedLetOnly_3188_, lean_object* v_skipConstInApp_3189_, lean_object* v_skipInstances_3190_, lean_object* v_e_3191_, lean_object* v_a_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
uint8_t v_usedLetOnly_boxed_3198_; uint8_t v_skipConstInApp_boxed_3199_; uint8_t v_skipInstances_boxed_3200_; lean_object* v_res_3201_; 
v_usedLetOnly_boxed_3198_ = lean_unbox(v_usedLetOnly_3188_);
v_skipConstInApp_boxed_3199_ = lean_unbox(v_skipConstInApp_3189_);
v_skipInstances_boxed_3200_ = lean_unbox(v_skipInstances_3190_);
v_res_3201_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__5(v_pre_3186_, v_post_3187_, v_usedLetOnly_boxed_3198_, v_skipConstInApp_boxed_3199_, v_skipInstances_boxed_3200_, v_e_3191_, v_a_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v_a_3192_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4___boxed(lean_object* v_pre_3202_, lean_object* v_post_3203_, lean_object* v_usedLetOnly_3204_, lean_object* v_skipConstInApp_3205_, lean_object* v_skipInstances_3206_, lean_object* v_sz_3207_, lean_object* v_i_3208_, lean_object* v_bs_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v_usedLetOnly_boxed_3216_; uint8_t v_skipConstInApp_boxed_3217_; uint8_t v_skipInstances_boxed_3218_; size_t v_sz_boxed_3219_; size_t v_i_boxed_3220_; lean_object* v_res_3221_; 
v_usedLetOnly_boxed_3216_ = lean_unbox(v_usedLetOnly_3204_);
v_skipConstInApp_boxed_3217_ = lean_unbox(v_skipConstInApp_3205_);
v_skipInstances_boxed_3218_ = lean_unbox(v_skipInstances_3206_);
v_sz_boxed_3219_ = lean_unbox_usize(v_sz_3207_);
lean_dec(v_sz_3207_);
v_i_boxed_3220_ = lean_unbox_usize(v_i_3208_);
lean_dec(v_i_3208_);
v_res_3221_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__4(v_pre_3202_, v_post_3203_, v_usedLetOnly_boxed_3216_, v_skipConstInApp_boxed_3217_, v_skipInstances_boxed_3218_, v_sz_boxed_3219_, v_i_boxed_3220_, v_bs_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
lean_dec(v___y_3214_);
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v___y_3210_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___boxed(lean_object* v_pre_3222_, lean_object* v_post_3223_, lean_object* v_usedLetOnly_3224_, lean_object* v_skipConstInApp_3225_, lean_object* v_skipInstances_3226_, lean_object* v_e_3227_, lean_object* v_a_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
uint8_t v_usedLetOnly_boxed_3234_; uint8_t v_skipConstInApp_boxed_3235_; uint8_t v_skipInstances_boxed_3236_; lean_object* v_res_3237_; 
v_usedLetOnly_boxed_3234_ = lean_unbox(v_usedLetOnly_3224_);
v_skipConstInApp_boxed_3235_ = lean_unbox(v_skipConstInApp_3225_);
v_skipInstances_boxed_3236_ = lean_unbox(v_skipInstances_3226_);
v_res_3237_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3222_, v_post_3223_, v_usedLetOnly_boxed_3234_, v_skipConstInApp_boxed_3235_, v_skipInstances_boxed_3236_, v_e_3227_, v_a_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v_a_3228_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8___boxed(lean_object* v_pre_3238_, lean_object* v_post_3239_, lean_object* v_usedLetOnly_3240_, lean_object* v_skipConstInApp_3241_, lean_object* v_skipInstances_3242_, lean_object* v_fvars_3243_, lean_object* v_e_3244_, lean_object* v_a_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_){
_start:
{
uint8_t v_usedLetOnly_boxed_3251_; uint8_t v_skipConstInApp_boxed_3252_; uint8_t v_skipInstances_boxed_3253_; lean_object* v_res_3254_; 
v_usedLetOnly_boxed_3251_ = lean_unbox(v_usedLetOnly_3240_);
v_skipConstInApp_boxed_3252_ = lean_unbox(v_skipConstInApp_3241_);
v_skipInstances_boxed_3253_ = lean_unbox(v_skipInstances_3242_);
v_res_3254_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8(v_pre_3238_, v_post_3239_, v_usedLetOnly_boxed_3251_, v_skipConstInApp_boxed_3252_, v_skipInstances_boxed_3253_, v_fvars_3243_, v_e_3244_, v_a_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v_a_3245_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9___boxed(lean_object* v_pre_3255_, lean_object* v_post_3256_, lean_object* v_usedLetOnly_3257_, lean_object* v_skipConstInApp_3258_, lean_object* v_skipInstances_3259_, lean_object* v_fvars_3260_, lean_object* v_e_3261_, lean_object* v_a_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_usedLetOnly_boxed_3268_; uint8_t v_skipConstInApp_boxed_3269_; uint8_t v_skipInstances_boxed_3270_; lean_object* v_res_3271_; 
v_usedLetOnly_boxed_3268_ = lean_unbox(v_usedLetOnly_3257_);
v_skipConstInApp_boxed_3269_ = lean_unbox(v_skipConstInApp_3258_);
v_skipInstances_boxed_3270_ = lean_unbox(v_skipInstances_3259_);
v_res_3271_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__9(v_pre_3255_, v_post_3256_, v_usedLetOnly_boxed_3268_, v_skipConstInApp_boxed_3269_, v_skipInstances_boxed_3270_, v_fvars_3260_, v_e_3261_, v_a_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v_a_3262_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10___boxed(lean_object* v_pre_3272_, lean_object* v_post_3273_, lean_object* v_usedLetOnly_3274_, lean_object* v_skipConstInApp_3275_, lean_object* v_skipInstances_3276_, lean_object* v_fvars_3277_, lean_object* v_e_3278_, lean_object* v_a_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
uint8_t v_usedLetOnly_boxed_3285_; uint8_t v_skipConstInApp_boxed_3286_; uint8_t v_skipInstances_boxed_3287_; lean_object* v_res_3288_; 
v_usedLetOnly_boxed_3285_ = lean_unbox(v_usedLetOnly_3274_);
v_skipConstInApp_boxed_3286_ = lean_unbox(v_skipConstInApp_3275_);
v_skipInstances_boxed_3287_ = lean_unbox(v_skipInstances_3276_);
v_res_3288_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10(v_pre_3272_, v_post_3273_, v_usedLetOnly_boxed_3285_, v_skipConstInApp_boxed_3286_, v_skipInstances_boxed_3287_, v_fvars_3277_, v_e_3278_, v_a_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v_a_3279_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3289_, lean_object* v___x_3290_, lean_object* v_pre_3291_, lean_object* v_post_3292_, lean_object* v_usedLetOnly_3293_, lean_object* v_skipConstInApp_3294_, lean_object* v_skipInstances_3295_, lean_object* v_a_3296_, lean_object* v_b_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
uint8_t v_usedLetOnly_boxed_3304_; uint8_t v_skipConstInApp_boxed_3305_; uint8_t v_skipInstances_boxed_3306_; lean_object* v_res_3307_; 
v_usedLetOnly_boxed_3304_ = lean_unbox(v_usedLetOnly_3293_);
v_skipConstInApp_boxed_3305_ = lean_unbox(v_skipConstInApp_3294_);
v_skipInstances_boxed_3306_ = lean_unbox(v_skipInstances_3295_);
v_res_3307_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3289_, v___x_3290_, v_pre_3291_, v_post_3292_, v_usedLetOnly_boxed_3304_, v_skipConstInApp_boxed_3305_, v_skipInstances_boxed_3306_, v_a_3296_, v_b_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___x_3290_);
lean_dec(v_upperBound_3289_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11___boxed(lean_object* v_skipInstances_3308_, lean_object* v_pre_3309_, lean_object* v_post_3310_, lean_object* v_usedLetOnly_3311_, lean_object* v_skipConstInApp_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
uint8_t v_skipInstances_boxed_3322_; uint8_t v_usedLetOnly_boxed_3323_; uint8_t v_skipConstInApp_boxed_3324_; lean_object* v_res_3325_; 
v_skipInstances_boxed_3322_ = lean_unbox(v_skipInstances_3308_);
v_usedLetOnly_boxed_3323_ = lean_unbox(v_usedLetOnly_3311_);
v_skipConstInApp_boxed_3324_ = lean_unbox(v_skipConstInApp_3312_);
v_res_3325_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__11(v_skipInstances_boxed_3322_, v_pre_3309_, v_post_3310_, v_usedLetOnly_boxed_3323_, v_skipConstInApp_boxed_3324_, v_x_3313_, v_x_3314_, v_x_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
lean_dec(v___y_3320_);
lean_dec_ref(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
return v_res_3325_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_unsigned_to_nat(16u);
v___x_3328_ = lean_mk_array(v___x_3327_, v___x_3326_);
return v___x_3328_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v___x_3329_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__0);
v___x_3330_ = lean_unsigned_to_nat(0u);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v___x_3330_);
lean_ctor_set(v___x_3331_, 1, v___x_3329_);
return v___x_3331_;
}
}
static lean_object* _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__1);
v___x_3333_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_3333_, 0, lean_box(0));
lean_closure_set(v___x_3333_, 1, lean_box(0));
lean_closure_set(v___x_3333_, 2, v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(lean_object* v_input_3334_, lean_object* v_pre_3335_, lean_object* v_post_3336_, uint8_t v_usedLetOnly_3337_, uint8_t v_skipConstInApp_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v_a_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; 
v___x_3344_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_3345_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3344_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = 0;
v___x_3348_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3(v_pre_3335_, v_post_3336_, v_usedLetOnly_3337_, v_skipConstInApp_3338_, v___x_3347_, v_input_3334_, v_a_3346_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3350_, 0, lean_box(0));
lean_closure_set(v___x_3350_, 1, lean_box(0));
lean_closure_set(v___x_3350_, 2, v_a_3346_);
v___x_3351_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_3350_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3358_ == 0)
{
lean_object* v_unused_3359_; 
v_unused_3359_ = lean_ctor_get(v___x_3351_, 0);
lean_dec(v_unused_3359_);
v___x_3353_ = v___x_3351_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_dec(v___x_3351_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v_a_3349_);
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3349_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
else
{
lean_dec(v_a_3346_);
return v___x_3348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___boxed(lean_object* v_input_3360_, lean_object* v_pre_3361_, lean_object* v_post_3362_, lean_object* v_usedLetOnly_3363_, lean_object* v_skipConstInApp_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_){
_start:
{
uint8_t v_usedLetOnly_boxed_3370_; uint8_t v_skipConstInApp_boxed_3371_; lean_object* v_res_3372_; 
v_usedLetOnly_boxed_3370_ = lean_unbox(v_usedLetOnly_3363_);
v_skipConstInApp_boxed_3371_ = lean_unbox(v_skipConstInApp_3364_);
v_res_3372_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_input_3360_, v_pre_3361_, v_post_3362_, v_usedLetOnly_boxed_3370_, v_skipConstInApp_boxed_3371_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_);
lean_dec(v___y_3368_);
lean_dec_ref(v___y_3367_);
lean_dec(v___y_3366_);
lean_dec_ref(v___y_3365_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(lean_object* v_e_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v___f_3381_; lean_object* v___f_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
v___f_3381_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___f_3382_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__1));
v___x_3383_ = 0;
v___x_3384_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3(v_e_3375_, v___f_3382_, v___f_3381_, v___x_3383_, v___x_3383_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___boxed(lean_object* v_e_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v_res_3391_; 
v_res_3391_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_e_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(lean_object* v_upperBound_3392_, lean_object* v___x_3393_, lean_object* v_pre_3394_, lean_object* v_post_3395_, uint8_t v_usedLetOnly_3396_, uint8_t v_skipConstInApp_3397_, uint8_t v_skipInstances_3398_, lean_object* v___x_3399_, lean_object* v_inst_3400_, lean_object* v_R_3401_, lean_object* v_a_3402_, lean_object* v_b_3403_, lean_object* v_c_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___redArg(v_upperBound_3392_, v___x_3393_, v_pre_3394_, v_post_3395_, v_usedLetOnly_3396_, v_skipConstInApp_3397_, v_skipInstances_3398_, v_a_3402_, v_b_3403_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_3412_ = _args[0];
lean_object* v___x_3413_ = _args[1];
lean_object* v_pre_3414_ = _args[2];
lean_object* v_post_3415_ = _args[3];
lean_object* v_usedLetOnly_3416_ = _args[4];
lean_object* v_skipConstInApp_3417_ = _args[5];
lean_object* v_skipInstances_3418_ = _args[6];
lean_object* v___x_3419_ = _args[7];
lean_object* v_inst_3420_ = _args[8];
lean_object* v_R_3421_ = _args[9];
lean_object* v_a_3422_ = _args[10];
lean_object* v_b_3423_ = _args[11];
lean_object* v_c_3424_ = _args[12];
lean_object* v___y_3425_ = _args[13];
lean_object* v___y_3426_ = _args[14];
lean_object* v___y_3427_ = _args[15];
lean_object* v___y_3428_ = _args[16];
lean_object* v___y_3429_ = _args[17];
lean_object* v___y_3430_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_3431_; uint8_t v_skipConstInApp_boxed_3432_; uint8_t v_skipInstances_boxed_3433_; lean_object* v_res_3434_; 
v_usedLetOnly_boxed_3431_ = lean_unbox(v_usedLetOnly_3416_);
v_skipConstInApp_boxed_3432_ = lean_unbox(v_skipConstInApp_3417_);
v_skipInstances_boxed_3433_ = lean_unbox(v_skipInstances_3418_);
v_res_3434_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__6(v_upperBound_3412_, v___x_3413_, v_pre_3414_, v_post_3415_, v_usedLetOnly_boxed_3431_, v_skipConstInApp_boxed_3432_, v_skipInstances_boxed_3433_, v___x_3419_, v_inst_3420_, v_R_3421_, v_a_3422_, v_b_3423_, v_c_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec(v___x_3419_);
lean_dec_ref(v___x_3413_);
lean_dec(v_upperBound_3412_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(lean_object* v_00_u03b2_3435_, lean_object* v_m_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v___x_3438_; 
v___x_3438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_m_3436_, v_a_3437_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3439_, lean_object* v_m_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7(v_00_u03b2_3439_, v_m_3440_, v_a_3441_);
lean_dec_ref(v_a_3441_);
lean_dec_ref(v_m_3440_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(lean_object* v_00_u03b1_3443_, lean_object* v_name_3444_, uint8_t v_bi_3445_, lean_object* v_type_3446_, lean_object* v_k_3447_, uint8_t v_kind_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___redArg(v_name_3444_, v_bi_3445_, v_type_3446_, v_k_3447_, v_kind_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10___boxed(lean_object* v_00_u03b1_3456_, lean_object* v_name_3457_, lean_object* v_bi_3458_, lean_object* v_type_3459_, lean_object* v_k_3460_, lean_object* v_kind_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v_bi_boxed_3468_; uint8_t v_kind_boxed_3469_; lean_object* v_res_3470_; 
v_bi_boxed_3468_ = lean_unbox(v_bi_3458_);
v_kind_boxed_3469_ = lean_unbox(v_kind_3461_);
v_res_3470_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__8_spec__10(v_00_u03b1_3456_, v_name_3457_, v_bi_boxed_3468_, v_type_3459_, v_k_3460_, v_kind_boxed_3469_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec(v___y_3462_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(lean_object* v_00_u03b1_3471_, lean_object* v_name_3472_, lean_object* v_type_3473_, lean_object* v_val_3474_, lean_object* v_k_3475_, uint8_t v_nondep_3476_, uint8_t v_kind_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___redArg(v_name_3472_, v_type_3473_, v_val_3474_, v_k_3475_, v_nondep_3476_, v_kind_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13___boxed(lean_object* v_00_u03b1_3485_, lean_object* v_name_3486_, lean_object* v_type_3487_, lean_object* v_val_3488_, lean_object* v_k_3489_, lean_object* v_nondep_3490_, lean_object* v_kind_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
uint8_t v_nondep_boxed_3498_; uint8_t v_kind_boxed_3499_; lean_object* v_res_3500_; 
v_nondep_boxed_3498_ = lean_unbox(v_nondep_3490_);
v_kind_boxed_3499_ = lean_unbox(v_kind_3491_);
v_res_3500_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__10_spec__13(v_00_u03b1_3485_, v_name_3486_, v_type_3487_, v_val_3488_, v_k_3489_, v_nondep_boxed_3498_, v_kind_boxed_3499_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(lean_object* v_00_u03b1_3501_, lean_object* v_ref_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg(v_ref_3502_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___boxed(lean_object* v_00_u03b1_3509_, lean_object* v_ref_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16(v_00_u03b1_3509_, v_ref_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(lean_object* v_00_u03b1_3517_, lean_object* v_x_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; 
v___x_3525_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___redArg(v_x_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12___boxed(lean_object* v_00_u03b1_3526_, lean_object* v_x_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12(v_00_u03b1_3526_, v_x_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13(lean_object* v_00_u03b2_3535_, lean_object* v_m_3536_, lean_object* v_a_3537_, lean_object* v_b_3538_){
_start:
{
lean_object* v___x_3539_; 
v___x_3539_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13___redArg(v_m_3536_, v_a_3537_, v_b_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(lean_object* v_00_u03b2_3540_, lean_object* v_a_3541_, lean_object* v_x_3542_){
_start:
{
lean_object* v___x_3543_; 
v___x_3543_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___redArg(v_a_3541_, v_x_3542_);
return v___x_3543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b2_3544_, lean_object* v_a_3545_, lean_object* v_x_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7_spec__8(v_00_u03b2_3544_, v_a_3545_, v_x_3546_);
lean_dec(v_x_3546_);
lean_dec_ref(v_a_3545_);
return v_res_3547_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(lean_object* v_00_u03b2_3548_, lean_object* v_a_3549_, lean_object* v_x_3550_){
_start:
{
uint8_t v___x_3551_; 
v___x_3551_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___redArg(v_a_3549_, v_x_3550_);
return v___x_3551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18___boxed(lean_object* v_00_u03b2_3552_, lean_object* v_a_3553_, lean_object* v_x_3554_){
_start:
{
uint8_t v_res_3555_; lean_object* v_r_3556_; 
v_res_3555_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__18(v_00_u03b2_3552_, v_a_3553_, v_x_3554_);
lean_dec(v_x_3554_);
lean_dec_ref(v_a_3553_);
v_r_3556_ = lean_box(v_res_3555_);
return v_r_3556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19(lean_object* v_00_u03b2_3557_, lean_object* v_data_3558_){
_start:
{
lean_object* v___x_3559_; 
v___x_3559_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19___redArg(v_data_3558_);
return v___x_3559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20(lean_object* v_00_u03b2_3560_, lean_object* v_a_3561_, lean_object* v_b_3562_, lean_object* v_x_3563_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__20___redArg(v_a_3561_, v_b_3562_, v_x_3563_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20(lean_object* v_00_u03b2_3565_, lean_object* v_i_3566_, lean_object* v_source_3567_, lean_object* v_target_3568_){
_start:
{
lean_object* v___x_3569_; 
v___x_3569_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20___redArg(v_i_3566_, v_source_3567_, v_target_3568_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21(lean_object* v_00_u03b2_3570_, lean_object* v_x_3571_, lean_object* v_x_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__13_spec__19_spec__20_spec__21___redArg(v_x_3571_, v_x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(lean_object* v_opts_3574_, lean_object* v_opt_3575_){
_start:
{
lean_object* v_name_3576_; lean_object* v_defValue_3577_; lean_object* v_map_3578_; lean_object* v___x_3579_; 
v_name_3576_ = lean_ctor_get(v_opt_3575_, 0);
v_defValue_3577_ = lean_ctor_get(v_opt_3575_, 1);
v_map_3578_ = lean_ctor_get(v_opts_3574_, 0);
v___x_3579_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3578_, v_name_3576_);
if (lean_obj_tag(v___x_3579_) == 0)
{
uint8_t v___x_3580_; 
v___x_3580_ = lean_unbox(v_defValue_3577_);
return v___x_3580_;
}
else
{
lean_object* v_val_3581_; 
v_val_3581_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_val_3581_);
lean_dec_ref(v___x_3579_);
if (lean_obj_tag(v_val_3581_) == 1)
{
uint8_t v_v_3582_; 
v_v_3582_ = lean_ctor_get_uint8(v_val_3581_, 0);
lean_dec_ref(v_val_3581_);
return v_v_3582_;
}
else
{
uint8_t v___x_3583_; 
lean_dec(v_val_3581_);
v___x_3583_ = lean_unbox(v_defValue_3577_);
return v___x_3583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1___boxed(lean_object* v_opts_3584_, lean_object* v_opt_3585_){
_start:
{
uint8_t v_res_3586_; lean_object* v_r_3587_; 
v_res_3586_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_opts_3584_, v_opt_3585_);
lean_dec_ref(v_opt_3585_);
lean_dec_ref(v_opts_3584_);
v_r_3587_ = lean_box(v_res_3586_);
return v_r_3587_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0(void){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3588_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1(void){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__0);
v___x_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
return v___x_3590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_object* v_00_u03b2_3591_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3___closed__1);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(lean_object* v_e_3593_, lean_object* v_k_3594_, uint8_t v_cleanupAnnotations_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___f_3601_; uint8_t v___x_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___f_3601_ = lean_alloc_closure((void*)(l_Lean_Meta_letBoundedTelescope___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_processParamLet_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3601_, 0, v_k_3594_);
v___x_3602_ = 1;
v___x_3603_ = 0;
v___x_3604_ = lean_box(0);
v___x_3605_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_3593_, v___x_3602_, v___x_3603_, v___x_3602_, v___x_3603_, v___x_3604_, v___f_3601_, v_cleanupAnnotations_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3605_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3605_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
v_a_3614_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3605_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3605_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg___boxed(lean_object* v_e_3622_, lean_object* v_k_3623_, lean_object* v_cleanupAnnotations_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3630_; lean_object* v_res_3631_; 
v_cleanupAnnotations_boxed_3630_ = lean_unbox(v_cleanupAnnotations_3624_);
v_res_3631_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3622_, v_k_3623_, v_cleanupAnnotations_boxed_3630_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
return v_res_3631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(lean_object* v_00_u03b1_3632_, lean_object* v_e_3633_, lean_object* v_k_3634_, uint8_t v_cleanupAnnotations_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_e_3633_, v_k_3634_, v_cleanupAnnotations_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___boxed(lean_object* v_00_u03b1_3642_, lean_object* v_e_3643_, lean_object* v_k_3644_, lean_object* v_cleanupAnnotations_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3651_; lean_object* v_res_3652_; 
v_cleanupAnnotations_boxed_3651_ = lean_unbox(v_cleanupAnnotations_3645_);
v_res_3652_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6(v_00_u03b1_3642_, v_e_3643_, v_k_3644_, v_cleanupAnnotations_boxed_3651_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(lean_object* v_x_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_){
_start:
{
if (lean_obj_tag(v_x_3653_) == 5)
{
lean_object* v_fn_3660_; lean_object* v_arg_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_fn_3660_ = lean_ctor_get(v_x_3653_, 0);
lean_inc_ref(v_fn_3660_);
v_arg_3661_ = lean_ctor_get(v_x_3653_, 1);
lean_inc_ref(v_arg_3661_);
lean_dec_ref(v_x_3653_);
v___x_3662_ = lean_array_set(v_x_3654_, v_x_3655_, v_arg_3661_);
v___x_3663_ = lean_unsigned_to_nat(1u);
v___x_3664_ = lean_nat_sub(v_x_3655_, v___x_3663_);
lean_dec(v_x_3655_);
v_x_3653_ = v_fn_3660_;
v_x_3654_ = v___x_3662_;
v_x_3655_ = v___x_3664_;
goto _start;
}
else
{
lean_object* v___x_3666_; uint8_t v___x_3667_; 
lean_dec(v_x_3655_);
v___x_3666_ = ((lean_object*)(l_Lean_Elab_WF_isWfParam_x3f___closed__1));
v___x_3667_ = l_Lean_Expr_isConstOf(v_x_3653_, v___x_3666_);
lean_dec_ref(v_x_3653_);
if (v___x_3667_ == 0)
{
lean_dec_ref(v_x_3654_);
goto v___jp_3657_;
}
else
{
lean_object* v___x_3668_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v___x_3668_ = lean_unsigned_to_nat(2u);
v___x_3669_ = lean_array_get_size(v_x_3654_);
v___x_3670_ = lean_nat_dec_le(v___x_3668_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_dec_ref(v_x_3654_);
goto v___jp_3657_;
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3671_ = lean_unsigned_to_nat(1u);
v___x_3672_ = lean_array_fget(v_x_3654_, v___x_3671_);
v___x_3673_ = l_Array_toSubarray___redArg(v_x_3654_, v___x_3668_, v___x_3669_);
v___x_3674_ = l_Subarray_copy___redArg(v___x_3673_);
v___x_3675_ = l_Lean_mkAppN(v___x_3672_, v___x_3674_);
lean_dec_ref(v___x_3674_);
v___x_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
v___x_3677_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
v___x_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
return v___x_3678_;
}
}
}
v___jp_3657_:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l_Lean_Elab_WF_paramProj___closed__0));
v___x_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
return v___x_3659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg___boxed(lean_object* v_x_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_3679_, v_x_3680_, v_x_3681_);
return v_res_3683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0(lean_object* v_e_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_dummy_3690_; lean_object* v_nargs_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_dummy_3690_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3691_ = l_Lean_Expr_getAppNumArgs(v_e_3684_);
lean_inc(v_nargs_3691_);
v___x_3692_ = lean_mk_array(v_nargs_3691_, v_dummy_3690_);
v___x_3693_ = lean_unsigned_to_nat(1u);
v___x_3694_ = lean_nat_sub(v_nargs_3691_, v___x_3693_);
lean_dec(v_nargs_3691_);
v___x_3695_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_e_3684_, v___x_3692_, v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__0___boxed(lean_object* v_e_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Lean_Elab_WF_preprocess___lam__0(v_e_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(lean_object* v_ref_3703_){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__12_spec__16___redArg___closed__5);
v___x_3706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3706_, 0, v_ref_3703_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg___boxed(lean_object* v_ref_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3708_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(lean_object* v_x_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___y_3719_; lean_object* v_fileName_3728_; lean_object* v_fileMap_3729_; lean_object* v_options_3730_; lean_object* v_currRecDepth_3731_; lean_object* v_maxRecDepth_3732_; lean_object* v_ref_3733_; lean_object* v_currNamespace_3734_; lean_object* v_openDecls_3735_; lean_object* v_initHeartbeats_3736_; lean_object* v_maxHeartbeats_3737_; lean_object* v_quotContext_3738_; lean_object* v_currMacroScope_3739_; uint8_t v_diag_3740_; lean_object* v_cancelTk_x3f_3741_; uint8_t v_suppressElabErrors_3742_; lean_object* v_inheritedTraceOptions_3743_; uint8_t v___x_3744_; 
v_fileName_3728_ = lean_ctor_get(v___y_3715_, 0);
v_fileMap_3729_ = lean_ctor_get(v___y_3715_, 1);
v_options_3730_ = lean_ctor_get(v___y_3715_, 2);
v_currRecDepth_3731_ = lean_ctor_get(v___y_3715_, 3);
v_maxRecDepth_3732_ = lean_ctor_get(v___y_3715_, 4);
v_ref_3733_ = lean_ctor_get(v___y_3715_, 5);
v_currNamespace_3734_ = lean_ctor_get(v___y_3715_, 6);
v_openDecls_3735_ = lean_ctor_get(v___y_3715_, 7);
v_initHeartbeats_3736_ = lean_ctor_get(v___y_3715_, 8);
v_maxHeartbeats_3737_ = lean_ctor_get(v___y_3715_, 9);
v_quotContext_3738_ = lean_ctor_get(v___y_3715_, 10);
v_currMacroScope_3739_ = lean_ctor_get(v___y_3715_, 11);
v_diag_3740_ = lean_ctor_get_uint8(v___y_3715_, sizeof(void*)*14);
v_cancelTk_x3f_3741_ = lean_ctor_get(v___y_3715_, 12);
v_suppressElabErrors_3742_ = lean_ctor_get_uint8(v___y_3715_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3743_ = lean_ctor_get(v___y_3715_, 13);
v___x_3744_ = lean_nat_dec_eq(v_currRecDepth_3731_, v_maxRecDepth_3732_);
if (v___x_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3745_ = lean_unsigned_to_nat(1u);
v___x_3746_ = lean_nat_add(v_currRecDepth_3731_, v___x_3745_);
lean_inc_ref(v_inheritedTraceOptions_3743_);
lean_inc(v_cancelTk_x3f_3741_);
lean_inc(v_currMacroScope_3739_);
lean_inc(v_quotContext_3738_);
lean_inc(v_maxHeartbeats_3737_);
lean_inc(v_initHeartbeats_3736_);
lean_inc(v_openDecls_3735_);
lean_inc(v_currNamespace_3734_);
lean_inc(v_ref_3733_);
lean_inc(v_maxRecDepth_3732_);
lean_inc_ref(v_options_3730_);
lean_inc_ref(v_fileMap_3729_);
lean_inc_ref(v_fileName_3728_);
v___x_3747_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3747_, 0, v_fileName_3728_);
lean_ctor_set(v___x_3747_, 1, v_fileMap_3729_);
lean_ctor_set(v___x_3747_, 2, v_options_3730_);
lean_ctor_set(v___x_3747_, 3, v___x_3746_);
lean_ctor_set(v___x_3747_, 4, v_maxRecDepth_3732_);
lean_ctor_set(v___x_3747_, 5, v_ref_3733_);
lean_ctor_set(v___x_3747_, 6, v_currNamespace_3734_);
lean_ctor_set(v___x_3747_, 7, v_openDecls_3735_);
lean_ctor_set(v___x_3747_, 8, v_initHeartbeats_3736_);
lean_ctor_set(v___x_3747_, 9, v_maxHeartbeats_3737_);
lean_ctor_set(v___x_3747_, 10, v_quotContext_3738_);
lean_ctor_set(v___x_3747_, 11, v_currMacroScope_3739_);
lean_ctor_set(v___x_3747_, 12, v_cancelTk_x3f_3741_);
lean_ctor_set(v___x_3747_, 13, v_inheritedTraceOptions_3743_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*14, v_diag_3740_);
lean_ctor_set_uint8(v___x_3747_, sizeof(void*)*14 + 1, v_suppressElabErrors_3742_);
lean_inc(v___y_3716_);
lean_inc(v___y_3714_);
lean_inc_ref(v___y_3713_);
lean_inc(v___y_3712_);
v___x_3748_ = lean_apply_6(v_x_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___x_3747_, v___y_3716_, lean_box(0));
v___y_3719_ = v___x_3748_;
goto v___jp_3718_;
}
else
{
lean_object* v___x_3749_; 
lean_dec_ref(v_x_3711_);
lean_inc(v_ref_3733_);
v___x_3749_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_3733_);
v___y_3719_ = v___x_3749_;
goto v___jp_3718_;
}
v___jp_3718_:
{
if (lean_obj_tag(v___y_3719_) == 0)
{
return v___y_3719_;
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v_a_3720_ = lean_ctor_get(v___y_3719_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___y_3719_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___y_3719_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___y_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg___boxed(lean_object* v_x_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_res_3757_; 
v_res_3757_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec(v___y_3751_);
return v_res_3757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(lean_object* v_pre_3758_, lean_object* v_post_3759_, size_t v_sz_3760_, size_t v_i_3761_, lean_object* v_bs_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
uint8_t v___x_3769_; 
v___x_3769_ = lean_usize_dec_lt(v_i_3761_, v_sz_3760_);
if (v___x_3769_ == 0)
{
lean_object* v___x_3770_; 
lean_dec_ref(v_post_3759_);
lean_dec_ref(v_pre_3758_);
v___x_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3770_, 0, v_bs_3762_);
return v___x_3770_;
}
else
{
lean_object* v_v_3771_; lean_object* v___x_3772_; 
v_v_3771_ = lean_array_uget_borrowed(v_bs_3762_, v_i_3761_);
lean_inc(v_v_3771_);
lean_inc_ref(v_post_3759_);
lean_inc_ref(v_pre_3758_);
v___x_3772_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3758_, v_post_3759_, v_v_3771_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
if (lean_obj_tag(v___x_3772_) == 0)
{
lean_object* v_a_3773_; lean_object* v___x_3774_; lean_object* v_bs_x27_3775_; size_t v___x_3776_; size_t v___x_3777_; lean_object* v___x_3778_; 
v_a_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_a_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = lean_unsigned_to_nat(0u);
v_bs_x27_3775_ = lean_array_uset(v_bs_3762_, v_i_3761_, v___x_3774_);
v___x_3776_ = ((size_t)1ULL);
v___x_3777_ = lean_usize_add(v_i_3761_, v___x_3776_);
v___x_3778_ = lean_array_uset(v_bs_x27_3775_, v_i_3761_, v_a_3773_);
v_i_3761_ = v___x_3777_;
v_bs_3762_ = v___x_3778_;
goto _start;
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref(v_bs_3762_);
lean_dec_ref(v_post_3759_);
lean_dec_ref(v_pre_3758_);
v_a_3780_ = lean_ctor_get(v___x_3772_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3772_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3772_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3772_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(lean_object* v_pre_3788_, lean_object* v_post_3789_, lean_object* v_x_3790_, lean_object* v_x_3791_, lean_object* v_x_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
if (lean_obj_tag(v_x_3790_) == 5)
{
lean_object* v_fn_3799_; lean_object* v_arg_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_fn_3799_ = lean_ctor_get(v_x_3790_, 0);
lean_inc_ref(v_fn_3799_);
v_arg_3800_ = lean_ctor_get(v_x_3790_, 1);
lean_inc_ref(v_arg_3800_);
lean_dec_ref(v_x_3790_);
v___x_3801_ = lean_array_set(v_x_3791_, v_x_3792_, v_arg_3800_);
v___x_3802_ = lean_unsigned_to_nat(1u);
v___x_3803_ = lean_nat_sub(v_x_3792_, v___x_3802_);
lean_dec(v_x_3792_);
v_x_3790_ = v_fn_3799_;
v_x_3791_ = v___x_3801_;
v_x_3792_ = v___x_3803_;
goto _start;
}
else
{
lean_object* v___x_3805_; 
lean_dec(v_x_3792_);
lean_inc_ref(v_post_3789_);
lean_inc_ref(v_pre_3788_);
v___x_3805_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3788_, v_post_3789_, v_x_3790_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; size_t v_sz_3807_; size_t v___x_3808_; lean_object* v___x_3809_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref(v___x_3805_);
v_sz_3807_ = lean_array_size(v_x_3791_);
v___x_3808_ = ((size_t)0ULL);
lean_inc_ref(v_post_3789_);
lean_inc_ref(v_pre_3788_);
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_3788_, v_post_3789_, v_sz_3807_, v___x_3808_, v_x_3791_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref(v___x_3809_);
v___x_3811_ = l_Lean_mkAppN(v_a_3806_, v_a_3810_);
lean_dec(v_a_3810_);
v___x_3812_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3788_, v_post_3789_, v___x_3811_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_);
return v___x_3812_;
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec(v_a_3806_);
lean_dec_ref(v_post_3789_);
lean_dec_ref(v_pre_3788_);
v_a_3813_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3809_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3809_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_dec_ref(v_x_3791_);
lean_dec_ref(v_post_3789_);
lean_dec_ref(v_pre_3788_);
return v___x_3805_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(lean_object* v_pre_3821_, lean_object* v_e_3822_, lean_object* v_post_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; uint8_t v___y_3838_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; uint8_t v___y_3851_; lean_object* v___y_3852_; uint8_t v___y_3853_; lean_object* v___y_3861_; lean_object* v___y_3862_; uint8_t v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; uint8_t v___y_3866_; lean_object* v___x_3873_; 
lean_inc_ref(v_pre_3821_);
lean_inc(v___y_3828_);
lean_inc_ref(v___y_3827_);
lean_inc(v___y_3826_);
lean_inc_ref(v___y_3825_);
lean_inc_ref(v_e_3822_);
v___x_3873_ = lean_apply_6(v_pre_3821_, v_e_3822_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, lean_box(0));
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3963_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3963_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3963_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v___y_3879_; 
switch(lean_obj_tag(v_a_3874_))
{
case 0:
{
lean_object* v_e_3953_; lean_object* v___x_3955_; 
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_e_3822_);
lean_dec_ref(v_pre_3821_);
v_e_3953_ = lean_ctor_get(v_a_3874_, 0);
lean_inc_ref(v_e_3953_);
lean_dec_ref(v_a_3874_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v_e_3953_);
v___x_3955_ = v___x_3876_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_e_3953_);
v___x_3955_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
return v___x_3955_;
}
}
case 1:
{
lean_object* v_e_3957_; lean_object* v___x_3958_; 
lean_del_object(v___x_3876_);
lean_dec_ref(v_e_3822_);
v_e_3957_ = lean_ctor_get(v_a_3874_, 0);
lean_inc_ref(v_e_3957_);
lean_dec_ref(v_a_3874_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3958_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_e_3957_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3960_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref(v___x_3958_);
v___x_3960_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v_a_3959_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3960_;
}
else
{
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3958_;
}
}
default: 
{
lean_object* v_e_x3f_3961_; 
lean_del_object(v___x_3876_);
v_e_x3f_3961_ = lean_ctor_get(v_a_3874_, 0);
lean_inc(v_e_x3f_3961_);
lean_dec_ref(v_a_3874_);
if (lean_obj_tag(v_e_x3f_3961_) == 0)
{
v___y_3879_ = v_e_3822_;
goto v___jp_3878_;
}
else
{
lean_object* v_val_3962_; 
lean_dec_ref(v_e_3822_);
v_val_3962_ = lean_ctor_get(v_e_x3f_3961_, 0);
lean_inc(v_val_3962_);
lean_dec_ref(v_e_x3f_3961_);
v___y_3879_ = v_val_3962_;
goto v___jp_3878_;
}
}
}
v___jp_3878_:
{
switch(lean_obj_tag(v___y_3879_))
{
case 7:
{
lean_object* v_binderName_3880_; lean_object* v_binderType_3881_; lean_object* v_body_3882_; uint8_t v_binderInfo_3883_; lean_object* v___x_3884_; 
v_binderName_3880_ = lean_ctor_get(v___y_3879_, 0);
lean_inc(v_binderName_3880_);
v_binderType_3881_ = lean_ctor_get(v___y_3879_, 1);
v_body_3882_ = lean_ctor_get(v___y_3879_, 2);
v_binderInfo_3883_ = lean_ctor_get_uint8(v___y_3879_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3881_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3884_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_binderType_3881_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v___x_3886_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref(v___x_3884_);
lean_inc_ref(v_body_3882_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3886_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_body_3882_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; size_t v___x_3888_; size_t v___x_3889_; uint8_t v___x_3890_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref(v___x_3886_);
v___x_3888_ = lean_ptr_addr(v_binderType_3881_);
v___x_3889_ = lean_ptr_addr(v_a_3885_);
v___x_3890_ = lean_usize_dec_eq(v___x_3888_, v___x_3889_);
if (v___x_3890_ == 0)
{
v___y_3861_ = v_a_3885_;
v___y_3862_ = v___y_3879_;
v___y_3863_ = v_binderInfo_3883_;
v___y_3864_ = v_a_3887_;
v___y_3865_ = v_binderName_3880_;
v___y_3866_ = v___x_3890_;
goto v___jp_3860_;
}
else
{
size_t v___x_3891_; size_t v___x_3892_; uint8_t v___x_3893_; 
v___x_3891_ = lean_ptr_addr(v_body_3882_);
v___x_3892_ = lean_ptr_addr(v_a_3887_);
v___x_3893_ = lean_usize_dec_eq(v___x_3891_, v___x_3892_);
v___y_3861_ = v_a_3885_;
v___y_3862_ = v___y_3879_;
v___y_3863_ = v_binderInfo_3883_;
v___y_3864_ = v_a_3887_;
v___y_3865_ = v_binderName_3880_;
v___y_3866_ = v___x_3893_;
goto v___jp_3860_;
}
}
else
{
lean_dec(v_a_3885_);
lean_dec(v_binderName_3880_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3886_;
}
}
else
{
lean_dec_ref(v___y_3879_);
lean_dec(v_binderName_3880_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3884_;
}
}
case 6:
{
lean_object* v_binderName_3894_; lean_object* v_binderType_3895_; lean_object* v_body_3896_; uint8_t v_binderInfo_3897_; lean_object* v___x_3898_; 
v_binderName_3894_ = lean_ctor_get(v___y_3879_, 0);
lean_inc(v_binderName_3894_);
v_binderType_3895_ = lean_ctor_get(v___y_3879_, 1);
v_body_3896_ = lean_ctor_get(v___y_3879_, 2);
v_binderInfo_3897_ = lean_ctor_get_uint8(v___y_3879_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_3895_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3898_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_binderType_3895_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3900_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
lean_inc(v_a_3899_);
lean_dec_ref(v___x_3898_);
lean_inc_ref(v_body_3896_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3900_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_body_3896_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; size_t v___x_3902_; size_t v___x_3903_; uint8_t v___x_3904_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref(v___x_3900_);
v___x_3902_ = lean_ptr_addr(v_binderType_3895_);
v___x_3903_ = lean_ptr_addr(v_a_3899_);
v___x_3904_ = lean_usize_dec_eq(v___x_3902_, v___x_3903_);
if (v___x_3904_ == 0)
{
v___y_3848_ = v_a_3901_;
v___y_3849_ = v___y_3879_;
v___y_3850_ = v_binderName_3894_;
v___y_3851_ = v_binderInfo_3897_;
v___y_3852_ = v_a_3899_;
v___y_3853_ = v___x_3904_;
goto v___jp_3847_;
}
else
{
size_t v___x_3905_; size_t v___x_3906_; uint8_t v___x_3907_; 
v___x_3905_ = lean_ptr_addr(v_body_3896_);
v___x_3906_ = lean_ptr_addr(v_a_3901_);
v___x_3907_ = lean_usize_dec_eq(v___x_3905_, v___x_3906_);
v___y_3848_ = v_a_3901_;
v___y_3849_ = v___y_3879_;
v___y_3850_ = v_binderName_3894_;
v___y_3851_ = v_binderInfo_3897_;
v___y_3852_ = v_a_3899_;
v___y_3853_ = v___x_3907_;
goto v___jp_3847_;
}
}
else
{
lean_dec(v_a_3899_);
lean_dec(v_binderName_3894_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3900_;
}
}
else
{
lean_dec_ref(v___y_3879_);
lean_dec(v_binderName_3894_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3898_;
}
}
case 8:
{
lean_object* v_declName_3908_; lean_object* v_type_3909_; lean_object* v_value_3910_; lean_object* v_body_3911_; uint8_t v_nondep_3912_; lean_object* v___x_3913_; 
v_declName_3908_ = lean_ctor_get(v___y_3879_, 0);
lean_inc(v_declName_3908_);
v_type_3909_ = lean_ctor_get(v___y_3879_, 1);
v_value_3910_ = lean_ctor_get(v___y_3879_, 2);
v_body_3911_ = lean_ctor_get(v___y_3879_, 3);
lean_inc_ref(v_body_3911_);
v_nondep_3912_ = lean_ctor_get_uint8(v___y_3879_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_3909_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3913_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_type_3909_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref(v___x_3913_);
lean_inc_ref(v_value_3910_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3915_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_value_3910_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref(v___x_3915_);
lean_inc_ref(v_body_3911_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3917_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_body_3911_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; size_t v___x_3919_; size_t v___x_3920_; uint8_t v___x_3921_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref(v___x_3917_);
v___x_3919_ = lean_ptr_addr(v_type_3909_);
v___x_3920_ = lean_ptr_addr(v_a_3914_);
v___x_3921_ = lean_usize_dec_eq(v___x_3919_, v___x_3920_);
if (v___x_3921_ == 0)
{
v___y_3831_ = v_nondep_3912_;
v___y_3832_ = v_declName_3908_;
v___y_3833_ = v_body_3911_;
v___y_3834_ = v_a_3916_;
v___y_3835_ = v_a_3914_;
v___y_3836_ = v___y_3879_;
v___y_3837_ = v_a_3918_;
v___y_3838_ = v___x_3921_;
goto v___jp_3830_;
}
else
{
size_t v___x_3922_; size_t v___x_3923_; uint8_t v___x_3924_; 
v___x_3922_ = lean_ptr_addr(v_value_3910_);
v___x_3923_ = lean_ptr_addr(v_a_3916_);
v___x_3924_ = lean_usize_dec_eq(v___x_3922_, v___x_3923_);
v___y_3831_ = v_nondep_3912_;
v___y_3832_ = v_declName_3908_;
v___y_3833_ = v_body_3911_;
v___y_3834_ = v_a_3916_;
v___y_3835_ = v_a_3914_;
v___y_3836_ = v___y_3879_;
v___y_3837_ = v_a_3918_;
v___y_3838_ = v___x_3924_;
goto v___jp_3830_;
}
}
else
{
lean_dec(v_a_3916_);
lean_dec(v_a_3914_);
lean_dec_ref(v_body_3911_);
lean_dec(v_declName_3908_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3917_;
}
}
else
{
lean_dec(v_a_3914_);
lean_dec_ref(v_body_3911_);
lean_dec(v_declName_3908_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3915_;
}
}
else
{
lean_dec_ref(v_body_3911_);
lean_dec(v_declName_3908_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3913_;
}
}
case 5:
{
lean_object* v_dummy_3925_; lean_object* v_nargs_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_dummy_3925_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2___closed__0);
v_nargs_3926_ = l_Lean_Expr_getAppNumArgs(v___y_3879_);
lean_inc(v_nargs_3926_);
v___x_3927_ = lean_mk_array(v_nargs_3926_, v_dummy_3925_);
v___x_3928_ = lean_unsigned_to_nat(1u);
v___x_3929_ = lean_nat_sub(v_nargs_3926_, v___x_3928_);
lean_dec(v_nargs_3926_);
v___x_3930_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_3821_, v_post_3823_, v___y_3879_, v___x_3927_, v___x_3929_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3930_;
}
case 10:
{
lean_object* v_data_3931_; lean_object* v_expr_3932_; lean_object* v___x_3933_; 
v_data_3931_ = lean_ctor_get(v___y_3879_, 0);
v_expr_3932_ = lean_ctor_get(v___y_3879_, 1);
lean_inc_ref(v_expr_3932_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3933_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_expr_3932_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; size_t v___x_3935_; size_t v___x_3936_; uint8_t v___x_3937_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v___x_3935_ = lean_ptr_addr(v_expr_3932_);
v___x_3936_ = lean_ptr_addr(v_a_3934_);
v___x_3937_ = lean_usize_dec_eq(v___x_3935_, v___x_3936_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_inc(v_data_3931_);
lean_dec_ref(v___y_3879_);
v___x_3938_ = l_Lean_Expr_mdata___override(v_data_3931_, v_a_3934_);
v___x_3939_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3938_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3939_;
}
else
{
lean_object* v___x_3940_; 
lean_dec(v_a_3934_);
v___x_3940_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___y_3879_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3940_;
}
}
else
{
lean_dec_ref(v___y_3879_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3933_;
}
}
case 11:
{
lean_object* v_typeName_3941_; lean_object* v_idx_3942_; lean_object* v_struct_3943_; lean_object* v___x_3944_; 
v_typeName_3941_ = lean_ctor_get(v___y_3879_, 0);
v_idx_3942_ = lean_ctor_get(v___y_3879_, 1);
v_struct_3943_ = lean_ctor_get(v___y_3879_, 2);
lean_inc_ref(v_struct_3943_);
lean_inc_ref(v_post_3823_);
lean_inc_ref(v_pre_3821_);
v___x_3944_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_3821_, v_post_3823_, v_struct_3943_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; size_t v___x_3946_; size_t v___x_3947_; uint8_t v___x_3948_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref(v___x_3944_);
v___x_3946_ = lean_ptr_addr(v_struct_3943_);
v___x_3947_ = lean_ptr_addr(v_a_3945_);
v___x_3948_ = lean_usize_dec_eq(v___x_3946_, v___x_3947_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; lean_object* v___x_3950_; 
lean_inc(v_idx_3942_);
lean_inc(v_typeName_3941_);
lean_dec_ref(v___y_3879_);
v___x_3949_ = l_Lean_Expr_proj___override(v_typeName_3941_, v_idx_3942_, v_a_3945_);
v___x_3950_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3949_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3950_;
}
else
{
lean_object* v___x_3951_; 
lean_dec(v_a_3945_);
v___x_3951_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___y_3879_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3951_;
}
}
else
{
lean_dec_ref(v___y_3879_);
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_pre_3821_);
return v___x_3944_;
}
}
default: 
{
lean_object* v___x_3952_; 
v___x_3952_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___y_3879_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3952_;
}
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec_ref(v_post_3823_);
lean_dec_ref(v_e_3822_);
lean_dec_ref(v_pre_3821_);
v_a_3964_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3873_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3873_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
v___jp_3830_:
{
if (v___y_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
lean_dec_ref(v___y_3836_);
lean_dec_ref(v___y_3833_);
v___x_3839_ = l_Lean_Expr_letE___override(v___y_3832_, v___y_3835_, v___y_3834_, v___y_3837_, v___y_3831_);
v___x_3840_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3839_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3840_;
}
else
{
size_t v___x_3841_; size_t v___x_3842_; uint8_t v___x_3843_; 
v___x_3841_ = lean_ptr_addr(v___y_3833_);
lean_dec_ref(v___y_3833_);
v___x_3842_ = lean_ptr_addr(v___y_3837_);
v___x_3843_ = lean_usize_dec_eq(v___x_3841_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_object* v___x_3844_; lean_object* v___x_3845_; 
lean_dec_ref(v___y_3836_);
v___x_3844_ = l_Lean_Expr_letE___override(v___y_3832_, v___y_3835_, v___y_3834_, v___y_3837_, v___y_3831_);
v___x_3845_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3844_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3845_;
}
else
{
lean_object* v___x_3846_; 
lean_dec_ref(v___y_3837_);
lean_dec_ref(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3832_);
v___x_3846_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___y_3836_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3846_;
}
}
}
v___jp_3847_:
{
if (v___y_3853_ == 0)
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec_ref(v___y_3849_);
v___x_3854_ = l_Lean_Expr_lam___override(v___y_3850_, v___y_3852_, v___y_3848_, v___y_3851_);
v___x_3855_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3854_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3855_;
}
else
{
uint8_t v___x_3856_; 
v___x_3856_ = l_Lean_instBEqBinderInfo_beq(v___y_3851_, v___y_3851_);
if (v___x_3856_ == 0)
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_dec_ref(v___y_3849_);
v___x_3857_ = l_Lean_Expr_lam___override(v___y_3850_, v___y_3852_, v___y_3848_, v___y_3851_);
v___x_3858_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3857_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3858_;
}
else
{
lean_object* v___x_3859_; 
lean_dec_ref(v___y_3852_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3848_);
v___x_3859_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___y_3849_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3859_;
}
}
}
v___jp_3860_:
{
if (v___y_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
lean_dec_ref(v___y_3862_);
v___x_3867_ = l_Lean_Expr_forallE___override(v___y_3865_, v___y_3861_, v___y_3864_, v___y_3863_);
v___x_3868_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3867_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3868_;
}
else
{
uint8_t v___x_3869_; 
v___x_3869_ = l_Lean_instBEqBinderInfo_beq(v___y_3863_, v___y_3863_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_dec_ref(v___y_3862_);
v___x_3870_ = l_Lean_Expr_forallE___override(v___y_3865_, v___y_3861_, v___y_3864_, v___y_3863_);
v___x_3871_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___x_3870_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3871_;
}
else
{
lean_object* v___x_3872_; 
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec_ref(v___y_3861_);
v___x_3872_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_3821_, v_post_3823_, v___y_3862_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_);
return v___x_3872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed(lean_object* v_pre_3972_, lean_object* v_e_3973_, lean_object* v_post_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1(v_pre_3972_, v_e_3973_, v_post_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(lean_object* v_pre_3982_, lean_object* v_post_3983_, lean_object* v_e_3984_, lean_object* v_a_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
lean_inc(v_a_3985_);
v___x_3991_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3991_, 0, lean_box(0));
lean_closure_set(v___x_3991_, 1, lean_box(0));
lean_closure_set(v___x_3991_, 2, v_a_3985_);
v___x_3992_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___x_3991_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4023_; 
v_a_3993_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_3995_ = v___x_3992_;
v_isShared_3996_ = v_isSharedCheck_4023_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3992_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4023_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3_spec__7___redArg(v_a_3993_, v_e_3984_);
lean_dec(v_a_3993_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v___f_3998_; lean_object* v___x_3999_; 
lean_del_object(v___x_3995_);
lean_inc_ref(v_e_3984_);
v___f_3998_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___lam__1___boxed), 9, 3);
lean_closure_set(v___f_3998_, 0, v_pre_3982_);
lean_closure_set(v___f_3998_, 1, v_e_3984_);
lean_closure_set(v___f_3998_, 2, v_post_3983_);
v___x_3999_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v___f_3998_, v_a_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; lean_object* v___f_4001_; lean_object* v___x_4002_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_n(v_a_4000_, 2);
lean_dec_ref(v___x_3999_);
lean_inc(v_a_3985_);
v___f_4001_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4001_, 0, v_a_3985_);
lean_closure_set(v___f_4001_, 1, v_e_3984_);
lean_closure_set(v___f_4001_, 2, v_a_4000_);
v___x_4002_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3_spec__3___lam__0(lean_box(0), v___f_4001_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4009_ == 0)
{
lean_object* v_unused_4010_; 
v_unused_4010_ = lean_ctor_get(v___x_4002_, 0);
lean_dec(v_unused_4010_);
v___x_4004_ = v___x_4002_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_dec(v___x_4002_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v_a_4000_);
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4000_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec(v_a_4000_);
v_a_4011_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4002_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4002_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
else
{
lean_dec_ref(v_e_3984_);
return v___x_3999_;
}
}
else
{
lean_object* v_val_4019_; lean_object* v___x_4021_; 
lean_dec_ref(v_e_3984_);
lean_dec_ref(v_post_3983_);
lean_dec_ref(v_pre_3982_);
v_val_4019_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_val_4019_);
lean_dec_ref(v___x_3997_);
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v_val_4019_);
v___x_4021_ = v___x_3995_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_val_4019_);
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
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec_ref(v_e_3984_);
lean_dec_ref(v_post_3983_);
lean_dec_ref(v_pre_3982_);
v_a_4024_ = lean_ctor_get(v___x_3992_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_3992_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_3992_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_3992_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(lean_object* v_pre_4032_, lean_object* v_post_4033_, lean_object* v_e_4034_, lean_object* v_a_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
lean_inc_ref(v_post_4033_);
lean_inc(v___y_4039_);
lean_inc_ref(v___y_4038_);
lean_inc(v___y_4037_);
lean_inc_ref(v___y_4036_);
lean_inc_ref(v_e_4034_);
v___x_4041_ = lean_apply_6(v_post_4033_, v_e_4034_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, lean_box(0));
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4060_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4060_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4060_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
switch(lean_obj_tag(v_a_4042_))
{
case 0:
{
lean_object* v_e_4046_; lean_object* v___x_4048_; 
lean_dec_ref(v_e_4034_);
lean_dec_ref(v_post_4033_);
lean_dec_ref(v_pre_4032_);
v_e_4046_ = lean_ctor_get(v_a_4042_, 0);
lean_inc_ref(v_e_4046_);
lean_dec_ref(v_a_4042_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v_e_4046_);
v___x_4048_ = v___x_4044_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_e_4046_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
case 1:
{
lean_object* v_e_4050_; lean_object* v___x_4051_; 
lean_del_object(v___x_4044_);
lean_dec_ref(v_e_4034_);
v_e_4050_ = lean_ctor_get(v_a_4042_, 0);
lean_inc_ref(v_e_4050_);
lean_dec_ref(v_a_4042_);
v___x_4051_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4032_, v_post_4033_, v_e_4050_, v_a_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_);
return v___x_4051_;
}
default: 
{
lean_object* v_e_x3f_4052_; 
lean_dec_ref(v_post_4033_);
lean_dec_ref(v_pre_4032_);
v_e_x3f_4052_ = lean_ctor_get(v_a_4042_, 0);
lean_inc(v_e_x3f_4052_);
lean_dec_ref(v_a_4042_);
if (lean_obj_tag(v_e_x3f_4052_) == 0)
{
lean_object* v___x_4054_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v_e_4034_);
v___x_4054_ = v___x_4044_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_e_4034_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
else
{
lean_object* v_val_4056_; lean_object* v___x_4058_; 
lean_dec_ref(v_e_4034_);
v_val_4056_ = lean_ctor_get(v_e_x3f_4052_, 0);
lean_inc(v_val_4056_);
lean_dec_ref(v_e_x3f_4052_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v_val_4056_);
v___x_4058_ = v___x_4044_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_val_4056_);
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
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec_ref(v_e_4034_);
lean_dec_ref(v_post_4033_);
lean_dec_ref(v_pre_4032_);
v_a_4061_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4041_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4041_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7___boxed(lean_object* v_pre_4069_, lean_object* v_post_4070_, lean_object* v_e_4071_, lean_object* v_a_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__7(v_pre_4069_, v_post_4070_, v_e_4071_, v_a_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v_a_4072_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6___boxed(lean_object* v_pre_4079_, lean_object* v_post_4080_, lean_object* v_sz_4081_, lean_object* v_i_4082_, lean_object* v_bs_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
size_t v_sz_boxed_4090_; size_t v_i_boxed_4091_; lean_object* v_res_4092_; 
v_sz_boxed_4090_ = lean_unbox_usize(v_sz_4081_);
lean_dec(v_sz_4081_);
v_i_boxed_4091_ = lean_unbox_usize(v_i_4082_);
lean_dec(v_i_4082_);
v_res_4092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__6(v_pre_4079_, v_post_4080_, v_sz_boxed_4090_, v_i_boxed_4091_, v_bs_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8___boxed(lean_object* v_pre_4093_, lean_object* v_post_4094_, lean_object* v_x_4095_, lean_object* v_x_4096_, lean_object* v_x_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__8(v_pre_4093_, v_post_4094_, v_x_4095_, v_x_4096_, v_x_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
lean_dec(v___y_4098_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4___boxed(lean_object* v_pre_4105_, lean_object* v_post_4106_, lean_object* v_e_4107_, lean_object* v_a_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4105_, v_post_4106_, v_e_4107_, v_a_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
lean_dec(v_a_4108_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(lean_object* v_input_4115_, lean_object* v_pre_4116_, lean_object* v_post_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v_a_4125_; lean_object* v___x_4126_; 
v___x_4123_ = lean_obj_once(&l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2, &l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2_once, _init_l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___closed__2);
v___x_4124_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4123_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref(v___x_4124_);
v___x_4126_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4(v_pre_4116_, v_post_4117_, v_input_4115_, v_a_4125_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref(v___x_4126_);
v___x_4128_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4128_, 0, lean_box(0));
lean_closure_set(v___x_4128_, 1, lean_box(0));
lean_closure_set(v___x_4128_, 2, v_a_4125_);
v___x_4129_ = l_Lean_Meta_transform___at___00__private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet_spec__3___lam__0(lean_box(0), v___x_4128_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4136_ == 0)
{
lean_object* v_unused_4137_; 
v_unused_4137_ = lean_ctor_get(v___x_4129_, 0);
lean_dec(v_unused_4137_);
v___x_4131_ = v___x_4129_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_dec(v___x_4129_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
lean_ctor_set(v___x_4131_, 0, v_a_4127_);
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4127_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
else
{
lean_dec(v_a_4125_);
return v___x_4126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4___boxed(lean_object* v_input_4138_, lean_object* v_pre_4139_, lean_object* v_post_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_input_4138_, v_pre_4139_, v_post_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
return v_res_4146_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0(void){
_start:
{
lean_object* v___x_4147_; double v___x_4148_; 
v___x_4147_ = lean_unsigned_to_nat(0u);
v___x_4148_ = lean_float_of_nat(v___x_4147_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(lean_object* v_cls_4152_, lean_object* v_msg_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_ref_4159_; lean_object* v___x_4160_; lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4205_; 
v_ref_4159_ = lean_ctor_get(v___y_4156_, 5);
v___x_4160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_WF_paramMatcher_spec__2_spec__2_spec__3_spec__9_spec__11_spec__13_spec__15_spec__16(v_msg_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4163_ = v___x_4160_;
v_isShared_4164_ = v_isSharedCheck_4205_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4205_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v_traceState_4166_; lean_object* v_env_4167_; lean_object* v_nextMacroScope_4168_; lean_object* v_ngen_4169_; lean_object* v_auxDeclNGen_4170_; lean_object* v_cache_4171_; lean_object* v_messages_4172_; lean_object* v_infoState_4173_; lean_object* v_snapshotTasks_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4204_; 
v___x_4165_ = lean_st_ref_take(v___y_4157_);
v_traceState_4166_ = lean_ctor_get(v___x_4165_, 4);
v_env_4167_ = lean_ctor_get(v___x_4165_, 0);
v_nextMacroScope_4168_ = lean_ctor_get(v___x_4165_, 1);
v_ngen_4169_ = lean_ctor_get(v___x_4165_, 2);
v_auxDeclNGen_4170_ = lean_ctor_get(v___x_4165_, 3);
v_cache_4171_ = lean_ctor_get(v___x_4165_, 5);
v_messages_4172_ = lean_ctor_get(v___x_4165_, 6);
v_infoState_4173_ = lean_ctor_get(v___x_4165_, 7);
v_snapshotTasks_4174_ = lean_ctor_get(v___x_4165_, 8);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4176_ = v___x_4165_;
v_isShared_4177_ = v_isSharedCheck_4204_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_snapshotTasks_4174_);
lean_inc(v_infoState_4173_);
lean_inc(v_messages_4172_);
lean_inc(v_cache_4171_);
lean_inc(v_traceState_4166_);
lean_inc(v_auxDeclNGen_4170_);
lean_inc(v_ngen_4169_);
lean_inc(v_nextMacroScope_4168_);
lean_inc(v_env_4167_);
lean_dec(v___x_4165_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4204_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
uint64_t v_tid_4178_; lean_object* v_traces_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4203_; 
v_tid_4178_ = lean_ctor_get_uint64(v_traceState_4166_, sizeof(void*)*1);
v_traces_4179_ = lean_ctor_get(v_traceState_4166_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v_traceState_4166_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4181_ = v_traceState_4166_;
v_isShared_4182_ = v_isSharedCheck_4203_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_traces_4179_);
lean_dec(v_traceState_4166_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4203_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4183_; double v___x_4184_; uint8_t v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4193_; 
v___x_4183_ = lean_box(0);
v___x_4184_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0, &l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__0);
v___x_4185_ = 0;
v___x_4186_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__1));
v___x_4187_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4187_, 0, v_cls_4152_);
lean_ctor_set(v___x_4187_, 1, v___x_4183_);
lean_ctor_set(v___x_4187_, 2, v___x_4186_);
lean_ctor_set_float(v___x_4187_, sizeof(void*)*3, v___x_4184_);
lean_ctor_set_float(v___x_4187_, sizeof(void*)*3 + 8, v___x_4184_);
lean_ctor_set_uint8(v___x_4187_, sizeof(void*)*3 + 16, v___x_4185_);
v___x_4188_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___closed__2));
v___x_4189_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4187_);
lean_ctor_set(v___x_4189_, 1, v_a_4161_);
lean_ctor_set(v___x_4189_, 2, v___x_4188_);
lean_inc(v_ref_4159_);
v___x_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4190_, 0, v_ref_4159_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = l_Lean_PersistentArray_push___redArg(v_traces_4179_, v___x_4190_);
if (v_isShared_4182_ == 0)
{
lean_ctor_set(v___x_4181_, 0, v___x_4191_);
v___x_4193_ = v___x_4181_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4191_);
lean_ctor_set_uint64(v_reuseFailAlloc_4202_, sizeof(void*)*1, v_tid_4178_);
v___x_4193_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4195_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 4, v___x_4193_);
v___x_4195_ = v___x_4176_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_env_4167_);
lean_ctor_set(v_reuseFailAlloc_4201_, 1, v_nextMacroScope_4168_);
lean_ctor_set(v_reuseFailAlloc_4201_, 2, v_ngen_4169_);
lean_ctor_set(v_reuseFailAlloc_4201_, 3, v_auxDeclNGen_4170_);
lean_ctor_set(v_reuseFailAlloc_4201_, 4, v___x_4193_);
lean_ctor_set(v_reuseFailAlloc_4201_, 5, v_cache_4171_);
lean_ctor_set(v_reuseFailAlloc_4201_, 6, v_messages_4172_);
lean_ctor_set(v_reuseFailAlloc_4201_, 7, v_infoState_4173_);
lean_ctor_set(v_reuseFailAlloc_4201_, 8, v_snapshotTasks_4174_);
v___x_4195_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4196_ = lean_st_ref_set(v___y_4157_, v___x_4195_);
v___x_4197_ = lean_box(0);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v___x_4197_);
v___x_4199_ = v___x_4163_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4197_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5___boxed(lean_object* v_cls_4206_, lean_object* v_msg_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v_cls_4206_, v_msg_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(size_t v_sz_4214_, size_t v_i_4215_, lean_object* v_bs_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_){
_start:
{
uint8_t v___x_4222_; 
v___x_4222_ = lean_usize_dec_lt(v_i_4215_, v_sz_4214_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; 
v___x_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4223_, 0, v_bs_4216_);
return v___x_4223_;
}
else
{
lean_object* v_v_4224_; lean_object* v___x_4225_; 
v_v_4224_ = lean_array_uget_borrowed(v_bs_4216_, v_i_4215_);
lean_inc(v_v_4224_);
v___x_4225_ = l_Lean_Elab_WF_mkWfParam(v_v_4224_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; lean_object* v_bs_x27_4228_; size_t v___x_4229_; size_t v___x_4230_; lean_object* v___x_4231_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref(v___x_4225_);
v___x_4227_ = lean_unsigned_to_nat(0u);
v_bs_x27_4228_ = lean_array_uset(v_bs_4216_, v_i_4215_, v___x_4227_);
v___x_4229_ = ((size_t)1ULL);
v___x_4230_ = lean_usize_add(v_i_4215_, v___x_4229_);
v___x_4231_ = lean_array_uset(v_bs_x27_4228_, v_i_4215_, v_a_4226_);
v_i_4215_ = v___x_4230_;
v_bs_4216_ = v___x_4231_;
goto _start;
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec_ref(v_bs_4216_);
v_a_4233_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4225_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4225_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2___boxed(lean_object* v_sz_4241_, lean_object* v_i_4242_, lean_object* v_bs_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
size_t v_sz_boxed_4249_; size_t v_i_boxed_4250_; lean_object* v_res_4251_; 
v_sz_boxed_4249_ = lean_unbox_usize(v_sz_4241_);
lean_dec(v_sz_4241_);
v_i_boxed_4250_ = lean_unbox_usize(v_i_4242_);
lean_dec(v_i_4242_);
v_res_4251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_boxed_4249_, v_i_boxed_4250_, v_bs_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
return v_res_4251_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0(void){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_4252_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4253_; 
v___x_4253_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_WF_preprocess_spec__3(lean_box(0));
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__1, &l_Lean_Elab_WF_preprocess___lam__2___closed__1_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__1);
v___x_4255_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__0, &l_Lean_Elab_WF_preprocess___lam__2___closed__0_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__0);
v___x_4256_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
lean_ctor_set(v___x_4256_, 2, v___x_4254_);
lean_ctor_set(v___x_4256_, 3, v___x_4254_);
return v___x_4256_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3(void){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4257_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4(void){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4258_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__3, &l_Lean_Elab_WF_preprocess___lam__2___closed__3_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__3);
v___x_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4258_);
return v___x_4259_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5(void){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4260_ = lean_unsigned_to_nat(0u);
v___x_4261_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4261_);
lean_ctor_set(v___x_4262_, 1, v___x_4260_);
return v___x_4262_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6(void){
_start:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = lean_unsigned_to_nat(32u);
v___x_4264_ = lean_mk_empty_array_with_capacity(v___x_4263_);
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
return v___x_4265_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7(void){
_start:
{
size_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4266_ = ((size_t)5ULL);
v___x_4267_ = lean_unsigned_to_nat(0u);
v___x_4268_ = lean_unsigned_to_nat(32u);
v___x_4269_ = lean_mk_empty_array_with_capacity(v___x_4268_);
v___x_4270_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__6, &l_Lean_Elab_WF_preprocess___lam__2___closed__6_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__6);
v___x_4271_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
lean_ctor_set(v___x_4271_, 1, v___x_4269_);
lean_ctor_set(v___x_4271_, 2, v___x_4267_);
lean_ctor_set(v___x_4271_, 3, v___x_4267_);
lean_ctor_set_usize(v___x_4271_, 4, v___x_4266_);
return v___x_4271_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__8(void){
_start:
{
lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4272_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__7, &l_Lean_Elab_WF_preprocess___lam__2___closed__7_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__7);
v___x_4273_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__4, &l_Lean_Elab_WF_preprocess___lam__2___closed__4_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__4);
v___x_4274_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4273_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
lean_ctor_set(v___x_4274_, 2, v___x_4273_);
lean_ctor_set(v___x_4274_, 3, v___x_4272_);
return v___x_4274_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__9(void){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__8, &l_Lean_Elab_WF_preprocess___lam__2___closed__8_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__8);
v___x_4276_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__5, &l_Lean_Elab_WF_preprocess___lam__2___closed__5_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__5);
v___x_4277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
lean_ctor_set(v___x_4277_, 1, v___x_4275_);
return v___x_4277_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14(void){
_start:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4286_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4287_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__13));
v___x_4288_ = l_Lean_Name_append(v___x_4287_, v___x_4286_);
return v___x_4288_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16(void){
_start:
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4290_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__15));
v___x_4291_ = l_Lean_stringToMessageData(v___x_4290_);
return v___x_4291_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18(void){
_start:
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4293_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__17));
v___x_4294_ = l_Lean_stringToMessageData(v___x_4293_);
return v___x_4294_;
}
}
static lean_object* _init_l_Lean_Elab_WF_preprocess___lam__2___closed__20(void){
_start:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__19));
v___x_4297_ = l_Lean_stringToMessageData(v___x_4296_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2(uint8_t v___x_4298_, lean_object* v_a_4299_, lean_object* v___f_4300_, lean_object* v___f_4301_, lean_object* v_xs_4302_, lean_object* v_x_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
size_t v_sz_4309_; size_t v___x_4310_; lean_object* v___x_4311_; 
v_sz_4309_ = lean_array_size(v_xs_4302_);
v___x_4310_ = ((size_t)0ULL);
lean_inc_ref(v_xs_4302_);
v___x_4311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_WF_preprocess_spec__2(v_sz_4309_, v___x_4310_, v_xs_4302_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref(v___x_4311_);
v___x_4313_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__2, &l_Lean_Elab_WF_preprocess___lam__2___closed__2_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__2);
v___x_4314_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramProj_declare__26___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_184633683____hygCtx___hyg_12_));
v___x_4315_ = l_Lean_Meta_Simp_Simprocs_add(v___x_4313_, v___x_4314_, v___x_4298_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; lean_object* v___x_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref(v___x_4315_);
v___x_4317_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramMatcher_declare__31___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_322181203____hygCtx___hyg_12_));
v___x_4318_ = 0;
v___x_4319_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4316_, v___x_4317_, v___x_4318_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref(v___x_4319_);
v___x_4321_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0____regBuiltin_Lean_Elab_WF_paramLet_declare__60___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Preprocess_2588207875____hygCtx___hyg_12_));
v___x_4322_ = l_Lean_Meta_Simp_Simprocs_add(v_a_4320_, v___x_4321_, v___x_4298_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4324_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
lean_inc(v_a_4323_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_getSimpContext___redArg(v___y_4304_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref(v___x_4324_);
v___x_4326_ = l_Lean_Expr_beta(v_a_4299_, v_a_4312_);
v___x_4327_ = lean_unsigned_to_nat(1u);
v___x_4328_ = lean_mk_empty_array_with_capacity(v___x_4327_);
v___x_4329_ = lean_array_push(v___x_4328_, v_a_4323_);
v___x_4330_ = lean_box(0);
v___x_4331_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__9, &l_Lean_Elab_WF_preprocess___lam__2___closed__9_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__9);
lean_inc_ref(v___x_4326_);
v___x_4332_ = l_Lean_Meta_simp(v___x_4326_, v_a_4325_, v___x_4329_, v___x_4330_, v___x_4331_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4332_) == 0)
{
lean_object* v_a_4333_; lean_object* v_fst_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4402_; 
v_a_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_a_4333_);
lean_dec_ref(v___x_4332_);
v_fst_4334_ = lean_ctor_get(v_a_4333_, 0);
v_isSharedCheck_4402_ = !lean_is_exclusive(v_a_4333_);
if (v_isSharedCheck_4402_ == 0)
{
lean_object* v_unused_4403_; 
v_unused_4403_ = lean_ctor_get(v_a_4333_, 1);
lean_dec(v_unused_4403_);
v___x_4336_ = v_a_4333_;
v_isShared_4337_ = v_isSharedCheck_4402_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_fst_4334_);
lean_dec(v_a_4333_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4402_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v_expr_4338_; lean_object* v_proof_x3f_4339_; uint8_t v_cache_4340_; lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4401_; 
v_expr_4338_ = lean_ctor_get(v_fst_4334_, 0);
v_proof_x3f_4339_ = lean_ctor_get(v_fst_4334_, 1);
v_cache_4340_ = lean_ctor_get_uint8(v_fst_4334_, sizeof(void*)*2);
v_isSharedCheck_4401_ = !lean_is_exclusive(v_fst_4334_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4342_ = v_fst_4334_;
v_isShared_4343_ = v_isSharedCheck_4401_;
goto v_resetjp_4341_;
}
else
{
lean_inc(v_proof_x3f_4339_);
lean_inc(v_expr_4338_);
lean_dec(v_fst_4334_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4401_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4344_; 
lean_inc_ref(v_expr_4338_);
v___x_4344_ = l_Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4(v_expr_4338_, v___f_4300_, v___f_4301_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4346_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_a_4345_);
lean_dec_ref(v___x_4344_);
v___x_4346_ = l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet(v_a_4345_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v_options_4357_; uint8_t v_hasTrace_4358_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref(v___x_4346_);
v_options_4357_ = lean_ctor_get(v___y_4306_, 2);
v_hasTrace_4358_ = lean_ctor_get_uint8(v_options_4357_, sizeof(void*)*1);
if (v_hasTrace_4358_ == 0)
{
lean_dec_ref(v_expr_4338_);
lean_del_object(v___x_4336_);
lean_dec_ref(v___x_4326_);
v___y_4349_ = v___y_4304_;
v___y_4350_ = v___y_4305_;
v___y_4351_ = v___y_4306_;
v___y_4352_ = v___y_4307_;
goto v___jp_4348_;
}
else
{
lean_object* v_inheritedTraceOptions_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; uint8_t v___x_4362_; 
v_inheritedTraceOptions_4359_ = lean_ctor_get(v___y_4306_, 13);
v___x_4360_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___lam__2___closed__11));
v___x_4361_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__14, &l_Lean_Elab_WF_preprocess___lam__2___closed__14_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__14);
v___x_4362_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4359_, v_options_4357_, v___x_4361_);
if (v___x_4362_ == 0)
{
lean_dec_ref(v_expr_4338_);
lean_del_object(v___x_4336_);
lean_dec_ref(v___x_4326_);
v___y_4349_ = v___y_4304_;
v___y_4350_ = v___y_4305_;
v___y_4351_ = v___y_4306_;
v___y_4352_ = v___y_4307_;
goto v___jp_4348_;
}
else
{
lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4366_; 
v___x_4363_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__16, &l_Lean_Elab_WF_preprocess___lam__2___closed__16_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__16);
v___x_4364_ = l_Lean_indentExpr(v___x_4326_);
if (v_isShared_4337_ == 0)
{
lean_ctor_set_tag(v___x_4336_, 7);
lean_ctor_set(v___x_4336_, 1, v___x_4364_);
lean_ctor_set(v___x_4336_, 0, v___x_4363_);
v___x_4366_ = v___x_4336_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v___x_4363_);
lean_ctor_set(v_reuseFailAlloc_4384_, 1, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4367_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__18, &l_Lean_Elab_WF_preprocess___lam__2___closed__18_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__18);
v___x_4368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4366_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = l_Lean_indentExpr(v_expr_4338_);
v___x_4370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4368_);
lean_ctor_set(v___x_4370_, 1, v___x_4369_);
v___x_4371_ = lean_obj_once(&l_Lean_Elab_WF_preprocess___lam__2___closed__20, &l_Lean_Elab_WF_preprocess___lam__2___closed__20_once, _init_l_Lean_Elab_WF_preprocess___lam__2___closed__20);
v___x_4372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4372_, 0, v___x_4370_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
lean_inc(v_a_4347_);
v___x_4373_ = l_Lean_indentExpr(v_a_4347_);
v___x_4374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4372_);
lean_ctor_set(v___x_4374_, 1, v___x_4373_);
v___x_4375_ = l_Lean_addTrace___at___00Lean_Elab_WF_preprocess_spec__5(v___x_4360_, v___x_4374_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_dec_ref(v___x_4375_);
v___y_4349_ = v___y_4304_;
v___y_4350_ = v___y_4305_;
v___y_4351_ = v___y_4306_;
v___y_4352_ = v___y_4307_;
goto v___jp_4348_;
}
else
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4383_; 
lean_dec(v_a_4347_);
lean_del_object(v___x_4342_);
lean_dec(v_proof_x3f_4339_);
lean_dec_ref(v_xs_4302_);
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4383_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4383_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4383_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4381_; 
if (v_isShared_4379_ == 0)
{
v___x_4381_ = v___x_4378_;
goto v_reusejp_4380_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_a_4376_);
v___x_4381_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4380_;
}
v_reusejp_4380_:
{
return v___x_4381_;
}
}
}
}
}
}
v___jp_4348_:
{
lean_object* v___x_4354_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set(v___x_4342_, 0, v_a_4347_);
v___x_4354_ = v___x_4342_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4347_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v_proof_x3f_4339_);
lean_ctor_set_uint8(v_reuseFailAlloc_4356_, sizeof(void*)*2, v_cache_4340_);
v___x_4354_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Lean_Meta_Simp_Result_addLambdas(v___x_4354_, v_xs_4302_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec_ref(v_xs_4302_);
return v___x_4355_;
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_del_object(v___x_4342_);
lean_dec(v_proof_x3f_4339_);
lean_dec_ref(v_expr_4338_);
lean_del_object(v___x_4336_);
lean_dec_ref(v___x_4326_);
lean_dec_ref(v_xs_4302_);
v_a_4385_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4346_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4346_);
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
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
lean_del_object(v___x_4342_);
lean_dec(v_proof_x3f_4339_);
lean_dec_ref(v_expr_4338_);
lean_del_object(v___x_4336_);
lean_dec_ref(v___x_4326_);
lean_dec_ref(v_xs_4302_);
v_a_4393_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4344_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4344_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec_ref(v___x_4326_);
lean_dec_ref(v_xs_4302_);
lean_dec_ref(v___f_4301_);
lean_dec_ref(v___f_4300_);
v_a_4404_ = lean_ctor_get(v___x_4332_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4332_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4332_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4332_);
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
lean_dec(v_a_4323_);
lean_dec(v_a_4312_);
lean_dec_ref(v_xs_4302_);
lean_dec_ref(v___f_4301_);
lean_dec_ref(v___f_4300_);
lean_dec_ref(v_a_4299_);
v_a_4412_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4324_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4324_);
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
lean_dec(v_a_4312_);
lean_dec_ref(v_xs_4302_);
lean_dec_ref(v___f_4301_);
lean_dec_ref(v___f_4300_);
lean_dec_ref(v_a_4299_);
v_a_4420_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4322_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4322_);
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
lean_dec(v_a_4312_);
lean_dec_ref(v_xs_4302_);
lean_dec_ref(v___f_4301_);
lean_dec_ref(v___f_4300_);
lean_dec_ref(v_a_4299_);
v_a_4428_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4430_ = v___x_4319_;
v_isShared_4431_ = v_isSharedCheck_4435_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_a_4428_);
lean_dec(v___x_4319_);
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
lean_dec(v_a_4312_);
lean_dec_ref(v_xs_4302_);
lean_dec_ref(v___f_4301_);
lean_dec_ref(v___f_4300_);
lean_dec_ref(v_a_4299_);
v_a_4436_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4315_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4315_);
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
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec_ref(v_xs_4302_);
lean_dec_ref(v___f_4301_);
lean_dec_ref(v___f_4300_);
lean_dec_ref(v_a_4299_);
v_a_4444_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4311_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4311_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___lam__2___boxed(lean_object* v___x_4452_, lean_object* v_a_4453_, lean_object* v___f_4454_, lean_object* v___f_4455_, lean_object* v_xs_4456_, lean_object* v_x_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
uint8_t v___x_14142__boxed_4463_; lean_object* v_res_4464_; 
v___x_14142__boxed_4463_ = lean_unbox(v___x_4452_);
v_res_4464_ = l_Lean_Elab_WF_preprocess___lam__2(v___x_14142__boxed_4463_, v_a_4453_, v___f_4454_, v___f_4455_, v_xs_4456_, v_x_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec_ref(v_x_4457_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess(lean_object* v_e_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_options_4472_; lean_object* v___x_4473_; uint8_t v___x_4474_; uint8_t v___x_4475_; 
v_options_4472_ = lean_ctor_get(v_a_4469_, 2);
v___x_4473_ = l_wf_preprocess;
v___x_4474_ = l_Lean_Option_get___at___00Lean_Elab_WF_preprocess_spec__1(v_options_4472_, v___x_4473_);
v___x_4475_ = 1;
if (v___x_4474_ == 0)
{
lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4476_ = lean_box(0);
v___x_4477_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4477_, 0, v_e_4466_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
lean_ctor_set_uint8(v___x_4477_, sizeof(void*)*2, v___x_4475_);
v___x_4478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
return v___x_4478_;
}
else
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Lean_Meta_letToHave(v_e_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___f_4481_; lean_object* v___f_4482_; lean_object* v___x_4483_; lean_object* v___f_4484_; uint8_t v___x_4485_; lean_object* v___x_4486_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc_n(v_a_4480_, 2);
lean_dec_ref(v___x_4479_);
v___f_4481_ = ((lean_object*)(l_Lean_Elab_WF_preprocess___closed__0));
v___f_4482_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Preprocess_0__Lean_Elab_WF_nonPropHaveToLet___closed__0));
v___x_4483_ = lean_box(v___x_4475_);
v___f_4484_ = lean_alloc_closure((void*)(l_Lean_Elab_WF_preprocess___lam__2___boxed), 11, 4);
lean_closure_set(v___f_4484_, 0, v___x_4483_);
lean_closure_set(v___f_4484_, 1, v_a_4480_);
lean_closure_set(v___f_4484_, 2, v___f_4481_);
lean_closure_set(v___f_4484_, 3, v___f_4482_);
v___x_4485_ = 0;
v___x_4486_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_WF_preprocess_spec__6___redArg(v_a_4480_, v___f_4484_, v___x_4485_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
return v___x_4486_;
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
v_a_4487_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4479_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4479_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_preprocess___boxed(lean_object* v_e_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_){
_start:
{
lean_object* v_res_4501_; 
v_res_4501_ = l_Lean_Elab_WF_preprocess(v_e_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_);
lean_dec(v_a_4499_);
lean_dec_ref(v_a_4498_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(lean_object* v_x_4502_, lean_object* v_x_4503_, lean_object* v_x_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
lean_object* v___x_4510_; 
v___x_4510_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___redArg(v_x_4502_, v_x_4503_, v_x_4504_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0___boxed(lean_object* v_x_4511_, lean_object* v_x_4512_, lean_object* v_x_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_WF_preprocess_spec__0(v_x_4511_, v_x_4512_, v_x_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(lean_object* v_00_u03b1_4520_, lean_object* v_ref_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___redArg(v_ref_4521_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4526_, lean_object* v_ref_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v_res_4531_; 
v_res_4531_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9_spec__11(v_00_u03b1_4526_, v_ref_4527_, v___y_4528_, v___y_4529_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(lean_object* v_00_u03b1_4532_, lean_object* v_x_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___redArg(v_x_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9___boxed(lean_object* v_00_u03b1_4541_, lean_object* v_x_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v_res_4549_; 
v_res_4549_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Elab_WF_preprocess_spec__4_spec__4_spec__9(v_00_u03b1_4541_, v_x_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
return v_res_4549_;
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
